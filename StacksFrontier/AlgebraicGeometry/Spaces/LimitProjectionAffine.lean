module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiAffineEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Representability
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfStructureSheaf

/-!
# The projections from an inverse limit of algebraic spaces are affine

Let `(X_i)` be a cofiltered inverse system of algebraic spaces over a scheme `S` with affine
transition morphisms, and let `X = lim X_i` be its limit as a presheaf on the big fppf site of
`S`.  Stacks 07SF, part (1), asserts that every projection `X ⟶ X_i` is affine.  The form of it in
`StacksFrontier.AlgebraicGeometry.Spaces.ApproximationSteps` asks the index category to be small
for the site — fewer objects, and fewer morphisms in each Hom-set, than the cofinality of the
size cutoff — because it builds the limit of the affine base changes inside the site from a
bound on the size of a colimit of rings.

This file proves the same assertion with no condition on the index category, when the limit
`X` is itself an algebraic space; that is the situation of a Noetherian approximation, where
`X` is the given space.  The size bound then comes from an atlas instead: the base change of
`X ⟶ X_i` along an affine scheme `Z ⟶ X_i` is an algebraic space, so it receives a locally
surjective morphism from an object `V` of the site, and the limit of the affine base changes,
computed among schemes, is cut down to the spectrum of the image of its ring in `Γ(V)`, which
has size below the cutoff.

## Main results

* `AlgebraicGeometry.BigFppfOver.exists_isLimit_isAffine_of_isLocallySurjective`: a cofiltered
  diagram of affine objects of the big fppf site of `S` has an affine limit in the site as soon
  as the limit of the presheaves it represents receives a locally surjective morphism from a
  representable presheaf.
* `AlgebraicGeometry.Space.isAffineHom_π_of_isAlgebraicSpace`: every projection from the limit
  of a cofiltered inverse system of presheaves with affine transition morphisms is affine,
  provided the limit and the target stage are algebraic spaces.
* `AlgebraicGeometry.Space.NoetherianApproximation.isAffineHom_π`: the projections of a
  Noetherian approximation of an algebraic space to its stages are affine.

## References

* [Stacks Project, Tag 07SF](https://stacks.math.columbia.edu/tag/07SF)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace BigFppfOver

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Global functions are separated for the big fppf topology over `S`: a global function on an
object of the site which vanishes on the members of a covering sieve vanishes. -/
theorem eq_zero_of_forall_mem_sieve {T : BigFppfOver B S hS} {R : Sieve T}
    (hR : R ∈ topology B S hS T) (a : Γ((toScheme B S hS).obj T, ⊤))
    (h : ∀ ⦃T' : BigFppfOver B S hS⦄ (f : T' ⟶ T), R f →
      ((toScheme B S hS).map f).appTop a = 0) : a = 0 := by
  have hR' : Sieve.overEquiv T R ∈ B.topology T.left := hR
  refine (BigFppfSite.isSheaf_globalSections B _ hR').isSeparatedFor.ext
    (t₁ := a) (t₂ := (0 : Γ(B.inclusion.obj T.left, ⊤))) fun Y g hg => ?_
  have := h (Over.homMk g : Over.mk (g ≫ T.hom) ⟶ T) ((Sieve.overEquiv_iff R g).1 hg)
  show (B.inclusion.map g).appTop a = (B.inclusion.map g).appTop 0
  rw [map_zero]
  exact this

section Limit

variable {J : Type u} [Category.{u} J] [IsCofiltered J]
  (W : J ⥤ BigFppfOver B S hS) [hW : ∀ k, IsAffine ((toScheme B S hS).obj (W.obj k))]
  {c : Cone (W ⋙ yoneda)} (hc : IsLimit c)

/-- The cofiltered diagram of the affine schemes of `W` has a limit among schemes. -/
instance : HasLimit (W ⋙ toScheme B S hS) :=
  have : ∀ k, IsAffine ((W ⋙ toScheme B S hS).obj k) := hW
  CofilteredLimit.hasLimit_of_isAffine _

/-- The cone over the schemes of `W` with vertex an object `T` of the site induced by a
`T`-point of the limit of the presheaves `W` represents. -/
noncomputable def limitPointCone {T : BigFppfOver B S hS} (x : yoneda.obj T ⟶ c.pt) :
    Cone (W ⋙ toScheme B S hS) where
  pt := (toScheme B S hS).obj T
  π :=
    { app := fun k => (toScheme B S hS).map (yoneda.preimage (x ≫ c.π.app k))
      naturality := fun k k' f => by
        have h : yoneda.preimage (x ≫ c.π.app k) ≫ W.map f =
            yoneda.preimage (x ≫ c.π.app k') := by
          apply yoneda.map_injective
          rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage, Category.assoc]
          exact congrArg (x ≫ ·) (c.w f)
        change 𝟙 _ ≫ (toScheme B S hS).map (yoneda.preimage (x ≫ c.π.app k')) =
          (toScheme B S hS).map (yoneda.preimage (x ≫ c.π.app k)) ≫
            (toScheme B S hS).map (W.map f)
        rw [Category.id_comp, ← Functor.map_comp, h] }

/-- The morphism of schemes from an object `T` of the site to the limit of the schemes of `W`
induced by a `T`-point of the limit of the presheaves `W` represents. -/
noncomputable def limitPoint {T : BigFppfOver B S hS} (x : yoneda.obj T ⟶ c.pt) :
    (toScheme B S hS).obj T ⟶ limit (W ⋙ toScheme B S hS) :=
  limit.lift _ (limitPointCone W x)

omit [IsCofiltered J] in
/-- The composite of `limitPoint W x` with the projection to the `k`-th stage is the morphism
of schemes underlying the `k`-th component of `x`. -/
@[reassoc (attr := simp)]
theorem limitPoint_π {T : BigFppfOver B S hS} (x : yoneda.obj T ⟶ c.pt) (k : J) :
    limitPoint W x ≫ limit.π _ k = (toScheme B S hS).map (yoneda.preimage (x ≫ c.π.app k)) :=
  limit.lift_π (limitPointCone W x) k

omit [IsCofiltered J] in
/-- `limitPoint` is natural in the object `T` of the site: precomposing the point with `g`
precomposes the morphism of schemes with the morphism underlying `g`. -/
theorem limitPoint_comp {T T' : BigFppfOver B S hS} (g : T' ⟶ T) (x : yoneda.obj T ⟶ c.pt) :
    limitPoint W (yoneda.map g ≫ x) = (toScheme B S hS).map g ≫ limitPoint W x := by
  refine limit.hom_ext fun k => ?_
  rw [Category.assoc, limitPoint_π, limitPoint_π, ← Functor.map_comp]
  have h : yoneda.preimage (yoneda.map g ≫ x ≫ c.π.app k) =
      g ≫ yoneda.preimage (x ≫ c.π.app k) := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
  rw [Category.assoc, h]

/-- The structure morphisms to `S` of the stages of `W`, read on the limit of their schemes, all
agree. -/
theorem limit_π_comp_hom (k k' : J) :
    limit.π (W ⋙ toScheme B S hS) k ≫ B.inclusion.map (W.obj k).hom =
      limit.π (W ⋙ toScheme B S hS) k' ≫ B.inclusion.map (W.obj k').hom := by
  have key : ∀ {m n : J} (f : m ⟶ n), limit.π (W ⋙ toScheme B S hS) n ≫
      B.inclusion.map (W.obj n).hom =
        limit.π (W ⋙ toScheme B S hS) m ≫ B.inclusion.map (W.obj m).hom := by
    intro m n f
    rw [← limit.w (W ⋙ toScheme B S hS) f, Category.assoc]
    congr 1
    exact (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map (Over.w (W.map f)))
  rw [key (IsCofiltered.minToLeft k k'), key (IsCofiltered.minToRight k k')]

/-- The limit of the affine schemes of `W` is affine. -/
instance : IsAffine (limit (W ⋙ toScheme B S hS)) :=
  have : ∀ k, IsAffine ((W ⋙ toScheme B S hS).obj k) := hW
  Scheme.isAffine_of_isLimit _ (limit.isLimit _)

section Cover

variable {V : BigFppfOver B S hS} (s : yoneda.obj V ⟶ c.pt)

/-- The kernel of the map on global functions `Γ(L) ⟶ Γ(V)` induced by `s`, where `L` is the
limit of the schemes of `W`. -/
noncomputable def coverIdeal : Ideal Γ(limit (W ⋙ toScheme B S hS), ⊤) :=
  RingHom.ker (limitPoint W s).appTop.hom

/-- The ring `Γ(L) / K` of the closed subscheme of `L` cut out by `coverIdeal`. -/
noncomputable abbrev coverRing : CommRingCat.{u} :=
  CommRingCat.of (Γ(limit (W ⋙ toScheme B S hS), ⊤) ⧸ coverIdeal W s)

/-- The quotient map `Γ(L) ⟶ Γ(L) / K`. -/
noncomputable abbrev coverQuot : Γ(limit (W ⋙ toScheme B S hS), ⊤) ⟶ coverRing W s :=
  CommRingCat.ofHom (Ideal.Quotient.mk _)

omit [IsCofiltered J] in
/-- `Spec (Γ(L) / K)` is an object of the site: its ring injects into `Γ(V)`. -/
theorem contains_spec_coverRing : B.Contains (Spec (coverRing W s)) :=
  Scheme.size_Spec_lt_of_injective_sections B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit
    (p := CommRingCat.ofHom (RingHom.kerLift (limitPoint W s).appTop.hom))
    (RingHom.kerLift_injective _) V.left.property

/-- The closed immersion `Spec (Γ(L) / K) ⟶ L`. -/
noncomputable def coverι : Spec (coverRing W s) ⟶ limit (W ⋙ toScheme B S hS) :=
  Spec.map (coverQuot W s) ≫ (limit (W ⋙ toScheme B S hS)).isoSpec.inv

/-- `coverι` is a closed immersion. -/
instance : IsClosedImmersion (coverι W s) := by
  have : IsClosedImmersion (Spec.map (coverQuot W s)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  rw [coverι]
  infer_instance

/-- `coverι` is a monomorphism. -/
instance : Mono (coverι W s) := by
  have : IsClosedImmersion (Spec.map (coverQuot W s)) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact mono_comp _ _

/-- A chosen index of the cofiltered category `J`. -/
noncomputable def someIndex : J := (IsCofiltered.nonempty (C := J)).some

/-- The structure morphism to `S` of `Spec (Γ(L) / K)`. -/
noncomputable def coverStr : Spec (coverRing W s) ⟶ S :=
  coverι W s ≫ limit.π (W ⋙ toScheme B S hS) someIndex ≫
    B.inclusion.map (W.obj someIndex).hom

/-- `Spec (Γ(L) / K)` as an object of the site. -/
noncomputable def coverObj : BigFppfOver B S hS :=
  BigFppfOver.mk B S hS (contains_spec_coverRing W s) (coverStr W s)

/-- The composite of `coverι` with the projection to any stage of `W` and that stage's structure
morphism to `S` is `coverStr`. -/
theorem coverι_π_comp_hom (k : J) :
    (coverι W s ≫ limit.π (W ⋙ toScheme B S hS) k) ≫ B.inclusion.map (W.obj k).hom =
      coverStr W s := by
  rw [Category.assoc, limit_π_comp_hom W k someIndex]
  rfl

/-- The cone over `W` with vertex `Spec (Γ(L) / K)`. -/
noncomputable def coverCone : Cone W where
  pt := coverObj W s
  π :=
    { app := fun k => Over.homMk
        (ObjectProperty.homMk (X := B.obj (contains_spec_coverRing W s)) (Y := (W.obj k).left)
          (coverι W s ≫ limit.π (W ⋙ toScheme B S hS) k))
        (by apply ObjectProperty.hom_ext; exact coverι_π_comp_hom W s k)
      naturality := fun k k' f => by
        apply (toScheme B S hS).map_injective
        change 𝟙 _ ≫ coverι W s ≫ limit.π (W ⋙ toScheme B S hS) k' =
          (coverι W s ≫ limit.π (W ⋙ toScheme B S hS) k) ≫ (W ⋙ toScheme B S hS).map f
        rw [Category.id_comp, Category.assoc, limit.w] }

/-- The morphism of schemes underlying the `k`-th projection of `coverCone` is `coverι`
followed by the `k`-th projection of the limit of the schemes of `W`. -/
theorem toScheme_map_coverCone_π (k : J) :
    (toScheme B S hS).map ((coverCone W s).π.app k) =
      coverι W s ≫ limit.π (W ⋙ toScheme B S hS) k :=
  rfl

variable {s} (hs : Presheaf.IsLocallySurjective (topology B S hS) s)
include hs

omit [IsCofiltered J] in
/-- The morphism to `L` induced by any point of `c.pt` with values in the site kills `K`: the
point lifts through `s` locally, and global functions are separated. -/
theorem limitPoint_appTop_eq_zero {T : BigFppfOver B S hS} (x : yoneda.obj T ⟶ c.pt)
    (a : Γ(limit (W ⋙ toScheme B S hS), ⊤)) (ha : a ∈ coverIdeal W s) :
    (limitPoint W x).appTop a = 0 := by
  refine eq_zero_of_forall_mem_sieve (hs.imageSieve_mem (yonedaEquiv x)) _
    fun T' f hf => ?_
  obtain ⟨h, hh⟩ := hf
  have hx : yoneda.map h ≫ s = yoneda.map f ≫ x := by
    apply yonedaEquiv.injective
    rwa [yonedaEquiv_comp, yonedaEquiv_yoneda_map, ← yonedaEquiv_naturality]
  have e1 : (toScheme B S hS).map f ≫ limitPoint W x =
      (toScheme B S hS).map h ≫ limitPoint W s := by
    rw [← limitPoint_comp, ← limitPoint_comp, hx]
  have e2 := congrArg (fun g : (toScheme B S hS).obj T' ⟶ limit (W ⋙ toScheme B S hS) =>
    g.appTop a) e1
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at e2
  rw [e2, show (limitPoint W s).appTop a = 0 from ha, map_zero]

/-- The factorization through `Spec (Γ(L) / K)` of the morphism to `L` induced by a point of
`c.pt` with values in the site. -/
noncomputable def coverLift {T : BigFppfOver B S hS} (x : yoneda.obj T ⟶ c.pt) :
    (toScheme B S hS).obj T ⟶ Spec (coverRing W s) :=
  ((toScheme B S hS).obj T).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.lift _ (limitPoint W x).appTop.hom (limitPoint_appTop_eq_zero W hs x)))

omit [IsCofiltered J] in
/-- `coverLift W hs x` composed with `coverι` is `limitPoint W x`. -/
theorem coverLift_ι {T : BigFppfOver B S hS} (x : yoneda.obj T ⟶ c.pt) :
    coverLift W hs x ≫ coverι W s = limitPoint W x := by
  rw [coverLift, coverι, Category.assoc, ← Category.assoc (Spec.map _), ← Spec.map_comp]
  have : coverQuot W s ≫ CommRingCat.ofHom (Ideal.Quotient.lift _ (limitPoint W x).appTop.hom
      (limitPoint_appTop_eq_zero W hs x)) = (limitPoint W x).appTop := by
    ext a
    rfl
  rw [this, ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc,
    Scheme.toSpecΓ_isoSpec_inv, Category.comp_id]

omit hs [IsCofiltered J] in
include hc in
/-- For a cone `e` over `W`, the morphism to the limit of the schemes of `W` induced by the point
of `c.pt` that `e` determines has `k`-th component the morphism underlying `e.π.app k`. -/
theorem limitPoint_lift_π (e : Cone W) (k : J) :
    limitPoint W (hc.lift (yoneda.mapCone e)) ≫ limit.π (W ⋙ toScheme B S hS) k =
      (toScheme B S hS).map (e.π.app k) := by
  rw [limitPoint_π, hc.fac]
  congr 1
  exact yoneda.preimage_map (e.π.app k)

include hc in
/-- `Spec (Γ(L) / K)` is the limit of `W` in the site. -/
noncomputable def isLimitCoverCone : IsLimit (coverCone W s) where
  lift e := BigFppfOver.homMk B S hS (contains_spec_coverRing W s) (coverStr W s)
    (coverLift W hs (hc.lift (yoneda.mapCone e))) (by
      rw [coverStr, ← Category.assoc, ← Category.assoc, coverLift_ι, limitPoint_lift_π W hc]
      exact (B.inclusion.map_comp _ _).symm.trans
        (congrArg B.inclusion.map (Over.w (e.π.app someIndex))))
  fac e k := by
    apply (toScheme B S hS).map_injective
    change coverLift W hs (hc.lift (yoneda.mapCone e)) ≫ coverι W s ≫
      limit.π (W ⋙ toScheme B S hS) k = _
    rw [← Category.assoc, coverLift_ι, limitPoint_lift_π W hc]
  uniq e m hm := by
    apply (toScheme B S hS).map_injective
    let mm : (toScheme B S hS).obj e.pt ⟶ Spec (coverRing W s) := (toScheme B S hS).map m
    have hmm : ∀ k, mm ≫ coverι W s ≫ limit.π (W ⋙ toScheme B S hS) k =
        (toScheme B S hS).map (e.π.app k) := fun k => by
      rw [← hm k, Functor.map_comp]
      rfl
    change mm = coverLift W hs (hc.lift (yoneda.mapCone e))
    refine (cancel_mono (coverι W s)).1 ?_
    rw [coverLift_ι]
    refine limit.hom_ext fun k => ?_
    rw [Category.assoc, limitPoint_lift_π W hc, hmm k]

include hc in
/-- **A cofiltered diagram of affine objects of the big fppf site whose represented limit is
covered by a representable has an affine limit in the site.**  Let `W` be a cofiltered diagram
of affine objects of the big fppf site of `S`, and let `c` be a limit cone of the presheaves they
represent.  If `c.pt` receives a locally surjective morphism from the presheaf represented by an
object `V` of the site, then `W` has a limit in the site, with affine underlying scheme.

No size condition is placed on the index.  The limit `L` of the underlying affine schemes exists
among schemes; the morphism `V ⟶ L` induced by the covering is a ring map `Γ(L) ⟶ Γ(V)` on
global functions, and the closed subscheme `Spec (Γ(L) / K)` of `L` cut out by its kernel `K` is
an object of the site, because `Γ(L) / K` injects into `Γ(V)`.  Every point of `c.pt` with values
in an object of the site lifts, locally, through `V`, so the corresponding morphism to `L` kills
`K` locally and hence, global functions being separated for the fppf topology, kills `K`: the
closed subscheme is the limit in the site. -/
theorem exists_isLimit_isAffine_of_isLocallySurjective :
    ∃ d : Cone W, IsAffine ((toScheme B S hS).obj d.pt) ∧ Nonempty (IsLimit d) :=
  ⟨coverCone W s, isAffine_Spec (coverRing W s),
    ⟨isLimitCoverCone W hc hs⟩⟩

end Cover

end Limit

end BigFppfOver

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 07SF, part (1), with no condition on the index.**  Let `D` be a cofiltered inverse
system of presheaves on the big fppf site of `S` with affine transition morphisms, and let `c` be
a limit cone of `D` whose vertex is an algebraic space.  Then the projection `c.pt ⟶ D i` to any
stage which is an algebraic space is affine.

Fix an affine object `Z` of the site and `g : Z ⟶ D i`.  By Stacks 07SF, part (2), the base
change `P = c.pt ×_{D i} Z` is the limit of the base changes of the stages over `i`, each of them
represented by an affine object of the site.  `P` is an algebraic space, so a scheme atlas of it
is locally surjective, and
`AlgebraicGeometry.BigFppfOver.exists_isLimit_isAffine_of_isLocallySurjective` gives an affine
limit of those affine objects in the site; it represents `P`. -/
theorem isAffineHom_π_of_isAlgebraicSpace {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hAffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom B S hS (D.map f))
    {c : Cone D} (hc : IsLimit c) (hX : IsAlgebraicSpace B S hS c.pt) (i : I)
    (hDi : IsAlgebraicSpace B S hS (D.obj i)) : IsAffineHom B S hS (c.π.app i) := by
  intro Z g
  set E := (Over.post (X := i) D ⋙ Over.pullback g) ⋙
    Over.forget (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj Z))
  have hbase : IsLimit ((Over.forget _).mapCone ((Over.pullback g).mapCone (c.overPost i))) := by
    have : IsConnected (Over i) := IsCofiltered.isConnected _
    exact isLimitOfPreserves (Over.forget _) (isLimitOfPreserves (Over.pullback g) (hc.overPost i))
  have hess : ∀ k : Over i,
      (BigAffineFppf.inclusion B S hS ⋙ yoneda).essImage (E.obj k) := by
    intro k
    obtain ⟨A, p, q, hpb⟩ := hAffine k.hom Z g
    exact ⟨A, ⟨hpb.isoPullback⟩⟩
  set F := BigAffineFppf.inclusion B S hS ⋙ yoneda
  set W := Functor.essImage.liftFunctor E F hess
  have hiso : W ⋙ F ≅ E := Functor.essImage.liftFunctorCompIso E F hess
  set W' := W ⋙ BigAffineFppf.inclusion B S hS
  have : ∀ k : Over i, IsAffine ((BigFppfOver.toScheme B S hS).obj (W'.obj k)) :=
    fun k => (W.obj k).property
  have hP := (IsLimit.postcomposeInvEquiv hiso _).symm hbase
  have hPalg : IsAlgebraicSpace B S hS (pullback (c.π.app i) g) :=
    isAlgebraicSpace_pullback B S hS _ _ hX
      (isAlgebraicSpace_yoneda B S hS ((BigAffineFppf.inclusion B S hS).obj Z)) hDi
  obtain ⟨V, a, haS, haE⟩ := hPalg.exists_atlas
  have ha := isLocallySurjective_of_surjective_etale B S hS a haS haE
  obtain ⟨d, hdaff, ⟨hd⟩⟩ :=
    BigFppfOver.exists_isLimit_isAffine_of_isLocallySurjective W' hP (s := a) ha
  have hyoneda : IsLimit ((Cone.postcompose hiso.hom).obj (yoneda.mapCone d)) :=
    (IsLimit.postcomposeHomEquiv hiso (yoneda.mapCone d)).symm (isLimitOfPreserves yoneda hd)
  have e : yoneda.obj d.pt ≅ pullback (c.π.app i) g :=
    hyoneda.conePointUniqueUpToIso hbase
  refine ⟨⟨d.pt, hdaff⟩, e.hom ≫ pullback.fst _ _,
    yoneda.preimage (e.hom ≫ pullback.snd _ _), ?_⟩
  exact IsPullback.of_iso_pullback ⟨by rw [Functor.map_preimage]; simp [pullback.condition]⟩
    e rfl (by rw [Functor.map_preimage])

/-- **The projections of a Noetherian approximation are affine.**  If `A` is a Noetherian
approximation of an algebraic space `X` — an inverse system of algebraic spaces with affine
transition morphisms whose limit is `X` — then every projection `X ⟶ X_j` is affine.

This is Stacks 07SF, part (1), in the form
`AlgebraicGeometry.Space.isAffineHom_π_of_isAlgebraicSpace`, which needs no condition on the
size of the index set. -/
theorem NoetherianApproximation.isAffineHom_π {hZ : B.Contains (⊤_ Scheme.{u})}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (A : NoetherianApproximation B S hS hZ X)
    (hX : IsAlgebraicSpace B S hS X) (j : letI := A.preorder; (A.I)ᵒᵖ) :
    letI := A.preorder
    IsAffineHom B S hS (A.π.app j) := by
  let := A.preorder
  let := A.nonempty
  let := A.isDirected
  let : IsCofiltered (A.I)ᵒᵖ := A.isCofiltered_op
  exact isAffineHom_π_of_isAlgebraicSpace B S hS A.diagram (fun g => A.isAffineHom_map g)
    A.isLimit hX j (A.isAlgebraicSpace j)

end Space

end AlgebraicGeometry

end

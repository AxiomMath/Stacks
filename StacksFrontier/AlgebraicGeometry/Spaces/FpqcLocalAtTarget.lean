module

public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Glueing.SmallSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteProperties
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.StandardCoverings
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.CategoryTheory.Extensive
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.MorphismProperty.Descent
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.PreservesLimits
public import Mathlib.CategoryTheory.Sites.Subcanonical
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver

/-!
# The fpqc locality criterion for properties of morphisms of algebraic spaces

A property `P` of morphisms of algebraic spaces over `S` is fpqc local on the base as soon as
it passes three tests: it is inherited by a morphism assembled from finitely many morphisms
along coproduct decompositions of source and target, it can be checked after pullback to every
affine scheme over the target, and it descends along a surjective flat morphism of affine
schemes. This is **Stacks 041J**, and it is the criterion through which concrete properties —
smoothness, flatness, finite presentation — are shown to be fpqc local on the base.

The proof reduces the assertion for an arbitrary fpqc covering to the affine case. An fpqc
covering of an affine scheme `T` admits, by definition, a finite subfamily that still covers;
the disjoint union `V` of that subfamily is affine, flat and surjective over `T`, and its
inclusions form a Zariski — hence fppf — covering of `V`. Testing `P` on the pullback along
`V → T` therefore suffices, and the descent hypothesis transports the conclusion back to `T`.

Two pieces of site theory make this work. The localized big fppf topology over `S` is
subcanonical, so representable sheaves are sheaves and a Zariski decomposition of a scheme
over `S` is a coproduct decomposition of the associated algebraic spaces; and the full
embedding of algebraic spaces into sheaves is full, faithful and preserves fibre products, so
coproducts and pullbacks may be computed in sheaves.

## Main results

* `AlgebraicGeometry.Space.isLocalAtTarget_fpqc_of_affineDescent`: **Stacks 041J**.

## References

* [Stacks Project, Tag 041J](https://stacks.math.columbia.edu/tag/041J)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v w x

/-- An algebraic space over `S`, regarded as a sheaf of sets on the big fppf site over `S`:
both categories are full subcategories of the presheaves, and an algebraic space is a sheaf. -/
noncomputable def algebraicSpacesToSheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    AlgebraicSpaces B S hS ⥤
      Sheaf (BigFppfOver.topology B S hS) (Type u) where
  obj X := ⟨X.obj, X.property.isSheaf⟩
  map f := ObjectProperty.homMk f.hom

/-- The inclusion of the algebraic spaces over `S` into the sheaves of sets is faithful. -/
theorem algebraicSpacesToSheaf_faithful
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (algebraicSpacesToSheaf B S hS).Faithful := by
  constructor
  intro X Y f g h
  apply ObjectProperty.hom_ext
  exact congrArg (fun k :
      (algebraicSpacesToSheaf B S hS).obj X ⟶
        (algebraicSpacesToSheaf B S hS).obj Y => k.hom) h

/-- The inclusion of the algebraic spaces over `S` into the sheaves of sets is full. -/
theorem algebraicSpacesToSheaf_full
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (algebraicSpacesToSheaf B S hS).Full := ⟨fun {_ _} f =>
      ⟨ObjectProperty.homMk f.hom, rfl⟩⟩

attribute [local instance] algebraicSpacesToSheaf_faithful algebraicSpacesToSheaf_full

private noncomputable def isColimit_algebraicSpaces_of_sheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type*} [Category* I] {F : I ⥤ AlgebraicSpaces B S hS}
    {c : Cocone F}
    (hc : IsColimit ((algebraicSpacesToSheaf B S hS).mapCocone c)) : IsColimit c :=
  isColimitOfReflects (algebraicSpacesToSheaf B S hS) hc

private theorem dependent_apply_cast {ι : Sort _} {A : ι → Sort _} {β : Sort _}
    (f : ∀ i, A i → β) {i j : ι} (h : i = j) (y : A j) :
    f i (h.symm ▸ y) = f j y := by
  cases h
  rfl

private alias empty_mem_bigFppfTopology :=
    AlgebraicGeometry.BigFppfSite.bot_mem_topology_obj_contains_empty

/-- The empty scheme, as an object of the big fppf site, has empty underlying scheme. -/
private theorem isEmpty_inclusion_obj_empty
    (B : BigFppfSite.{u}) (hE : B.Contains (∅ : Scheme.{u})) :
    IsEmpty (B.inclusion.obj (B.obj hE)) := by
  change IsEmpty (∅ : Scheme.{u})
  infer_instance

private theorem bottom_mem_bigFppfOver_of_isEmpty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z : BigFppfOver B S hS)
    (hZ : IsEmpty (B.inclusion.obj Z.left)) :
    (⊥ : Sieve Z) ∈ BigFppfOver.topology B S hS Z := by
  let hE : B.Contains (∅ : Scheme.{u}) :=
    lt_of_le_of_lt Scheme.size_empty_le_aleph0 B.aleph0_lt_cutoff
  let : IsEmpty (B.inclusion.obj (B.obj hE)) := isEmpty_inclusion_obj_empty B hE
  let eScheme : (B.inclusion.obj Z.left) ≅ (B.inclusion.obj (B.obj hE)) :=
    (isInitialOfIsEmpty : IsInitial (B.inclusion.obj Z.left)).uniqueUpToIso
      isInitialOfIsEmpty
  let e : Z.left ≅ B.obj hE := ObjectProperty.isoMk _ eScheme
  have hbot : (⊥ : Sieve Z.left) ∈ B.topology Z.left := by
    simpa using B.topology.pullback_stable e.hom
      (empty_mem_bigFppfTopology B hE)
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff]
  simpa using hbot

private noncomputable def isInitial_bigFppfOver_of_isEmpty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z : BigFppfOver B S hS)
    (hZ : IsEmpty (B.inclusion.obj Z.left)) : IsInitial Z :=
  IsInitial.ofUniqueHom
    (fun W => Over.homMk
      (B.inclusion.preimage (isInitialOfIsEmpty.to (B.inclusion.obj W.left)))
      (by
        apply B.inclusion.map_injective
        rw [B.inclusion.map_comp, B.inclusion.map_preimage]
        exact isInitialOfIsEmpty.hom_ext _ _))
    (fun W f => by
      apply Over.OverMorphism.ext
      apply B.inclusion.map_injective
      exact isInitialOfIsEmpty.hom_ext _ _)

private theorem isEmpty_bigFppfOver_left_of_isInitial
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (Z : BigFppfOver B S hS) (hZ : IsInitial Z) :
    IsEmpty (B.inclusion.obj Z.left) := by
  let hE : B.Contains (∅ : Scheme.{u}) :=
    lt_of_le_of_lt Scheme.size_empty_le_aleph0 B.aleph0_lt_cutoff
  let emptyOver : BigFppfOver B S hS :=
    Over.mk (B.inclusion.preimage
      (X := B.obj hE) (Y := B.obj hS)
      (Scheme.emptyTo (B.inclusion.obj (B.obj hS))))
  exact ⟨fun x =>
    (isEmpty_inclusion_obj_empty B hE).false (B.inclusion.map (hZ.to emptyOver).left x)⟩

private noncomputable def isColimitCofanMkUliftYoneda
    {C : Type w} [Category.{u} C] (J : GrothendieckTopology C) [J.Subcanonical]
    {I : Type x} {X : I → C} {Y : C} (ι : ∀ i, X i ⟶ Y)
    (hcover : Sieve.ofArrows X ι ∈ J Y) [∀ i, Mono (ι i)]
    (hempty : ∀ Z : C, IsInitial Z → ⊥ ∈ J Z)
    (hdisj : ∀ {i j : I}, i ≠ j → ∀ {Z : C} (a : Z ⟶ X i) (b : Z ⟶ X j),
      a ≫ ι i = b ≫ ι j → Nonempty (IsInitial Z)) :
    IsColimit (Cofan.mk (J.uliftYoneda.{v}.obj Y)
      (fun i => J.uliftYoneda.{v}.map (ι i))) := by
  classical
  have glue (s : Cofan (fun i => J.uliftYoneda.{v}.obj (X i))) :
      ∃! t : s.pt.obj.obj (Opposite.op Y),
        ∀ i, s.pt.obj.map (ι i).op t = J.uliftYonedaEquiv (s.inj i) := by
    apply (Presieve.isSheafFor_arrows_iff _ _).mp
      ((Presieve.isSheafFor_iff_generate _).mpr
        (s.pt.property.isSheafFor _ hcover))
    intro i j Z a b hab
    by_cases hij : i = j
    · subst j
      rw [(cancel_mono (ι i)).mp hab]
    · obtain ⟨hZ⟩ := hdisj hij a b hab
      have := Types.isTerminalEquivUnique _
        (Sheaf.isTerminalOfBotCover s.pt Z (hempty Z hZ))
      exact Subsingleton.elim _ _
  refine Cofan.IsColimit.mk _
    (fun s => J.uliftYonedaEquiv.symm (glue s).choose) ?_ ?_
  · intro s i
    apply J.uliftYonedaEquiv.injective
    change J.uliftYonedaEquiv
      (J.uliftYoneda.map (ι i) ≫ J.uliftYonedaEquiv.symm (glue s).choose) = _
    rw [← J.uliftYonedaEquiv_naturality, Equiv.apply_symm_apply]
    exact (glue s).choose_spec.1 i
  · intro s m hm
    apply J.uliftYonedaEquiv.injective
    rw [Equiv.apply_symm_apply]
    apply (glue s).choose_spec.2
    intro i
    rw [J.uliftYonedaEquiv_naturality]
    exact congrArg J.uliftYonedaEquiv (hm i)

private noncomputable def schemeSpaceCofanSheafIsColimit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type*} [Finite I] {X : I → BigFppfOver B S hS}
    {Y : BigFppfOver B S hS} (ι : ∀ i, X i ⟶ Y)
    (_hc : IsColimit (Cofan.mk Y ι))
    (hcover : Sieve.ofArrows X ι ∈
      BigFppfOver.topology B S hS Y)
    (hmono : ∀ i, Mono (ι i))
    (hempty : ∀ (Z : BigFppfOver B S hS), IsInitial Z →
      ⊥ ∈ BigFppfOver.topology B S hS Z)
    (hdisj : ∀ {i j : I} (_hij : i ≠ j) {Z : BigFppfOver B S hS}
      (a : Z ⟶ X i) (b : Z ⟶ X j), a ≫ ι i = b ≫ ι j → Nonempty (IsInitial Z)) :
    IsColimit (Cofan.mk
      ((algebraicSpacesToSheaf B S hS).obj (schemeSpace Y))
      (fun i => (algebraicSpacesToSheaf B S hS).map
        (schemeSpaceMap (ι i)))) := by
  let J := BigFppfOver.topology B S hS
  let : J.Subcanonical := bigFppfOver_subcanonical B S hS
  let : ∀ i, Mono ((Cofan.mk Y ι).inj i) := hmono
  let F := algebraicSpacesToSheaf B S hS
  let cF : Cofan (fun i => F.obj (schemeSpace (X i))) :=
    Cofan.mk (F.obj (schemeSpace Y)) (fun i => F.map (schemeSpaceMap (ι i)))
  let cJ : Cofan (fun i => J.yoneda.obj (X i)) :=
    Cofan.mk (J.yoneda.obj Y) (fun i => J.yoneda.map (ι i))
  let iso (Z : BigFppfOver B S hS) :
      J.yoneda.obj Z ≅ F.obj (schemeSpace Z) :=
    ObjectProperty.isoMk _ (Iso.refl _)
  let e : cJ ≅ cF := Cofan.ext (iso Y) (by
    intro i
    apply Sheaf.hom_ext
    rfl)
  have hcJ : IsColimit cJ := by
    simpa [cJ] using J.isColimitCofanMkYoneda (X := X) (c := Cofan.mk Y ι)
      hcover hempty hdisj
  exact IsColimit.ofIsoColimit hcJ e

private noncomputable def schemeSpaceCofanIsColimit
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {I : Type*} [Finite I] {X : I → BigFppfOver B S hS}
    {Y : BigFppfOver B S hS} (ι : ∀ i, X i ⟶ Y)
    (hc : IsColimit (Cofan.mk Y ι))
    (hcover : Sieve.ofArrows X ι ∈
      BigFppfOver.topology B S hS Y)
    (hmono : ∀ i, Mono (ι i))
    (hempty : ∀ (Z : BigFppfOver B S hS), IsInitial Z →
      ⊥ ∈ BigFppfOver.topology B S hS Z)
    (hdisj : ∀ {i j : I} (_hij : i ≠ j) {Z : BigFppfOver B S hS}
      (a : Z ⟶ X i) (b : Z ⟶ X j), a ≫ ι i = b ≫ ι j → Nonempty (IsInitial Z)) :
    IsColimit (Cofan.mk (schemeSpace Y)
      (fun i => schemeSpaceMap (ι i))) := by
  let F := algebraicSpacesToSheaf B S hS
  let c : Cofan (fun i => schemeSpace (X i)) :=
    Cofan.mk (schemeSpace Y) (fun i => schemeSpaceMap (ι i))
  exact isColimit_algebraicSpaces_of_sheaf B S hS
    ((Cofan.isColimitMapCoconeEquiv F (fun i => schemeSpace (X i)) c).symm
      (schemeSpaceCofanSheafIsColimit B S hS ι hc hcover hmono hempty hdisj))

private structure AffineCoproductData
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : BigAffineFppf B S hS}
    (U : PreZeroHypercover.{u + 1} T) [Finite U.I₀] where
  V : BigAffineFppf B S hS
  g : V ⟶ T
  coprodIso : (BigAffineFppf.toScheme B S hS).obj V ≅
    ∐ fun k : Shrink.{u, u + 1} U.I₀ =>
      (BigAffineFppf.toScheme B S hS).obj
        (U.X ((equivShrink.{u, u + 1} U.I₀).symm k))
  incl : ∀ j : Shrink.{u, u + 1} U.I₀,
    U.X ((equivShrink.{u, u + 1} U.I₀).symm j) ⟶ V
  fac : ∀ j, incl j ≫ g = U.f ((equivShrink.{u, u + 1} U.I₀).symm j)
  mapIncl : ∀ j, (BigAffineFppf.toScheme B S hS).map (incl j) ≫ coprodIso.hom =
    Sigma.ι (fun k : Shrink.{u, u + 1} U.I₀ =>
      (BigAffineFppf.toScheme B S hS).obj
        (U.X ((equivShrink.{u, u + 1} U.I₀).symm k))) j
  jointlySurjective : ∀ x, ∃ j y,
    (BigAffineFppf.toScheme B S hS).map (incl j) y = x

private noncomputable def affineCoproductData
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : BigAffineFppf B S hS}
    (U : PreZeroHypercover.{u + 1} T) [Finite U.I₀] :
    AffineCoproductData B S hS U := by
  let inc := BigAffineFppf.inclusion B S hS
  let e := equivShrink.{u, u + 1} U.I₀
  let : Finite (Shrink.{u, u + 1} U.I₀) := Finite.of_equiv U.I₀ e
  let : Countable (Shrink.{u, u + 1} U.I₀) := Finite.to_countable
  let F : Shrink.{u, u + 1} U.I₀ → Scheme.{u} :=
    fun i => (BigAffineFppf.toScheme B S hS).obj (U.X (e.symm i))
  let W : Scheme.{u} := ∐ F
  have hW : W.size < B.cutoff := by
    apply Scheme.size_sigmaObj_lt B.aleph0_lt_cutoff B.aleph0_lt_cutoff_cof
      (Cardinal.mk_le_aleph0) F
    intro i
    exact (inc.obj (U.X (e.symm i))).left.property
  let q_i : ∀ i, F i ⟶ S := fun i =>
    B.inclusion.map (inc.obj (U.X (e.symm i))).hom
  let q : W ⟶ S := Sigma.desc q_i
  let Wbase : BigFppfOver B S hS :=
    Over.mk (B.inclusion.preimage
      (show B.inclusion.obj (B.obj hW) ⟶ B.inclusion.obj (B.obj hS) from q))
  let V : BigAffineFppf B S hS := ⟨Wbase, by
    change IsAffine W
    infer_instance⟩
  let Vover := inc.obj V
  let Tover := inc.obj T
  let m : W ⟶ (BigAffineFppf.toScheme B S hS).obj T :=
    Sigma.desc fun i => (BigAffineFppf.toScheme B S hS).map (U.f (e.symm i))
  let msmall : Vover.left ⟶ Tover.left :=
    B.inclusion.preimage (show B.inclusion.obj Vover.left ⟶ B.inclusion.obj Tover.left from m)
  have hdesc (i) : Sigma.ι F i ≫ m =
      (BigAffineFppf.toScheme B S hS).map (U.f (e.symm i)) := by
    simp [m]
  have hV : B.inclusion.map Vover.hom = q := by
    dsimp [Vover, V, Wbase]
    change B.inclusion.map (B.inclusion.preimage
      (show B.inclusion.obj (B.obj hW) ⟶ B.inclusion.obj (B.obj hS) from q)) = q
    exact B.inclusion.map_preimage
      (show B.inclusion.obj (B.obj hW) ⟶ B.inclusion.obj (B.obj hS) from q)
  have hm : msmall ≫ Tover.hom = Vover.hom := by
    apply B.inclusion.map_injective
    change B.inclusion.map (B.inclusion.preimage
      (show B.inclusion.obj Vover.left ⟶ B.inclusion.obj Tover.left from m)) ≫
      B.inclusion.map Tover.hom =
      B.inclusion.map Vover.hom
    rw [B.inclusion.map_preimage]
    apply Sigma.hom_ext
    intro i
    change Sigma.ι F i ≫ m ≫ B.inclusion.map Tover.hom =
      Sigma.ι F i ≫ B.inclusion.map Vover.hom
    have hcomp :
        (BigAffineFppf.toScheme B S hS).map (U.f (e.symm i)) ≫
          B.inclusion.map Tover.hom = q_i i := by
      change B.inclusion.map (Over.Hom.left (inc.map (U.f (e.symm i)))) ≫
        B.inclusion.map Tover.hom = B.inclusion.map (inc.obj (U.X (e.symm i))).hom
      exact congrArg B.inclusion.map (Over.w (inc.map (U.f (e.symm i))))
    rw [hV]
    change Sigma.ι F i ≫ m ≫ B.inclusion.map Tover.hom = Sigma.ι F i ≫ q
    rw [← Category.assoc, hdesc i, hcomp]
    exact (Sigma.ι_desc q_i i).symm
  let g : V ⟶ T := ObjectProperty.homMk (Over.homMk msmall hm)
  let σ (i : Shrink.{u, u + 1} U.I₀) :
      B.inclusion.obj ((BigAffineFppf.inclusion B S hS).obj
        (U.X (e.symm i))).left ⟶ B.inclusion.obj Vover.left := by
    change F i ⟶ W
    exact Sigma.ι F i
  let α (i : Shrink.{u, u + 1} U.I₀) :
      (BigAffineFppf.inclusion B S hS).obj (U.X (e.symm i)) ⟶ Vover :=
    Over.homMk (B.inclusion.preimage (σ i)) (by
      apply B.inclusion.map_injective
      change B.inclusion.map (B.inclusion.preimage (σ i)) ≫
        B.inclusion.map Vover.hom =
          B.inclusion.map ((BigAffineFppf.inclusion B S hS).obj
            (U.X (e.symm i))).hom
      rw [B.inclusion.map_preimage, hV]
      change Sigma.ι F i ≫ q = q_i i
      exact Sigma.ι_desc q_i i)
  let ι (i : Shrink.{u, u + 1} U.I₀) :
      U.X (e.symm i) ⟶ V := ObjectProperty.homMk (α i)
  have hfac : ∀ i, ι i ≫ g = U.f (e.symm i) := by
    intro i
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    change B.inclusion.map (B.inclusion.preimage (σ i) ≫ msmall) =
      B.inclusion.map (Over.Hom.left (U.f (e.symm i)).hom)
    rw [B.inclusion.map_comp, B.inclusion.map_preimage, B.inclusion.map_preimage]
    exact hdesc i
  have hmapIncl : ∀ i, (BigAffineFppf.toScheme B S hS).map (ι i) =
      Sigma.ι F i := by
    intro i
    change B.inclusion.map (B.inclusion.preimage (σ i)) = Sigma.ι F i
    exact B.inclusion.map_preimage _
  exact ⟨V, g, Iso.refl W, ι, hfac, by
    intro j
    simpa [V, W, Wbase, F, e, BigAffineFppf.toScheme,
      BigFppfOver.toScheme, BigFppfOver.forget,
      BigFppfSite.inclusion, BigFppfSite.obj] using hmapIncl j,
    by
      intro x
      obtain ⟨z, hz⟩ := (AlgebraicGeometry.sigmaMk F).surjective x
      rcases z with ⟨j, y⟩
      refine ⟨j, y, ?_⟩
      calc
        (BigAffineFppf.toScheme B S hS).map (ι j) y = Sigma.ι F j y := by
          simpa [F, W, V, Wbase, BigAffineFppf.toScheme,
            BigFppfOver.toScheme, BigFppfOver.forget,
            BigFppfSite.inclusion, BigFppfSite.obj] using
              congrArg (fun f => f y) (hmapIncl j)
        _ = x := by simpa only [AlgebraicGeometry.sigmaMk_mk] using hz⟩

/-- Each inclusion of the affine coproduct is an open immersion of schemes. -/
private theorem isOpenImmersion_map_incl
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : BigAffineFppf B S hS} (U : PreZeroHypercover.{u + 1} T) [Finite U.I₀]
    (d : AffineCoproductData B S hS U) (j : Shrink.{u, u + 1} U.I₀) :
    IsOpenImmersion ((BigAffineFppf.toScheme B S hS).map (d.incl j)) := by
  have : IsOpenImmersion ((BigAffineFppf.toScheme B S hS).map (d.incl j) ≫ d.coprodIso.hom) := by
    rw [d.mapIncl j]
    exact (AlgebraicGeometry.sigmaOpenCover _).map_prop j
  exact IsOpenImmersion.of_comp _ d.coprodIso.hom

private theorem affineCoproduct_inclusions_cover
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : BigAffineFppf B S hS}
    (U : PreZeroHypercover.{u + 1} T) [Finite U.I₀]
    (d : AffineCoproductData B S hS U) :
    Sieve.ofArrows
      (fun i : Shrink.{u, u + 1} U.I₀ =>
        (BigAffineFppf.inclusion B S hS).obj
          (U.X ((equivShrink.{u, u + 1} U.I₀).symm i)))
      (fun i => (BigAffineFppf.inclusion B S hS).map (d.incl i)) ∈
      BigFppfOver.topology B S hS
        ((BigAffineFppf.inclusion B S hS).obj d.V) := by
  classical
  let inc := BigAffineFppf.inclusion B S hS
  let e := equivShrink.{u, u + 1} U.I₀
  let : Finite (Shrink.{u, u + 1} U.I₀) := Finite.of_equiv U.I₀ e
  let Vover := inc.obj d.V
  let Tsite := (BigFppfOver.forget B S hS).obj Vover
  let E : PreZeroHypercover Vover := {
    I₀ := Shrink.{u, u + 1} U.I₀
    X i := inc.obj (U.X (e.symm i))
    f i := inc.map (d.incl i) }
  let Esite := E.map (Over.forget (B.obj hS))
  let E' := Esite.map B.inclusion
  let : Finite E'.I₀ := Finite.of_equiv U.I₀ e
  have hopen (i : Shrink.{u, u + 1} U.I₀) : IsOpenImmersion (E'.f i) :=
    isOpenImmersion_map_incl B S hS U d i
  have hstandard : IsStandardFppfCovering E'.X E'.f := by
    refine IsStandardFppfCovering.mk inferInstance ?_ ?_ ?_ ?_ ?_
    · exact d.V.property
    · intro i
      exact (U.X (e.symm i)).property
    · intro i
      let : IsOpenImmersion (E'.f i) := hopen i
      infer_instance
    · intro i
      have hl : LocallyOfFinitePresentation (E'.f i) :=
        by
          let : IsOpenImmersion (E'.f i) := hopen i
          infer_instance
      let : IsAffine (E'.X i) := (U.X (e.symm i)).property
      let : IsAffine (B.inclusion.obj Tsite) := d.V.property
      let : IsAffineHom (E'.f i) := inferInstance
      have hqc : QuasiCompact (E'.f i) := inferInstance
      have hqs : QuasiSeparated (E'.f i) := by
        infer_instance
      exact FinitePresentation.mk hl hqc hqs
    · apply Set.eq_univ_iff_forall.mpr
      intro x
      obtain ⟨j, y, hy⟩ := d.jointlySurjective x
      refine Set.mem_iUnion.mpr ⟨j, ⟨y, ?_⟩⟩
      have hE : E'.f j = (BigAffineFppf.toScheme B S hS).map (d.incl j) := by
        rfl
      rw [hE]
      exact hy
  have hsurj : ∀ x, ∃ i, x ∈ Set.range (E'.f i) := by
    intro x
    have hx : x ∈ ⋃ i, Set.range (E'.f i) := by
      rw [hstandard.jointly_surjective]
      simp
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, ⟨y, hy⟩⟩
  have hprops : ∀ i, Flat (E'.f i) ∧ LocallyOfFinitePresentation (E'.f i) := by
    intro i
    exact ⟨hstandard.flat i, (hstandard.finite_presentation i).1⟩
  have hfp : E'.presieve₀ ∈ Scheme.fppfPrecoverage
      (B.inclusion.obj ((BigFppfOver.forget B S hS).obj Vover)) := by
    rw [Scheme.fppfPrecoverage_eq_inf]
    show (E'.presieve₀ ∈ Scheme.precoverage (@Flat : MorphismProperty Scheme.{u})
        (B.inclusion.obj ((BigFppfOver.forget B S hS).obj Vover))) ∧
      (E'.presieve₀ ∈ Scheme.precoverage
        (@LocallyOfFinitePresentation : MorphismProperty Scheme.{u})
        (B.inclusion.obj ((BigFppfOver.forget B S hS).obj Vover)))
    constructor
    · exact (Scheme.presieve₀_mem_precoverage_iff (P := @Flat) E').2
        ⟨hsurj, fun i => hprops i |>.1⟩
    · exact (Scheme.presieve₀_mem_precoverage_iff (P := @LocallyOfFinitePresentation) E').2
        ⟨hsurj, fun i => hprops i |>.2⟩
  obtain ⟨W, hW, htaut⟩ :=
    exists_isCovering_tautologicallyEquivalent_standardFppfCovering
      B ((BigFppfOver.forget B S hS).obj Vover) E' hfp hstandard
  have hWpre : W.presieve₀ ∈ B.precoverage Tsite := ⟨W, rfl, hW⟩
  have hWgen : Sieve.generate W.presieve₀ ∈ B.topology Tsite :=
    Precoverage.generate_mem_toGrothendieck hWpre
  have htautSite : PreZeroHypercover.TautologicallyEquivalent Esite W := by
    constructor
    · obtain ⟨α, hα⟩ := htaut.1
      refine ⟨α, ?_⟩
      intro i
      obtain ⟨iso, hiso⟩ := hα i
      refine ⟨ObjectProperty.isoMk _ iso, ?_⟩
      apply B.inclusion.map_injective
      show iso.hom ≫ (W.map B.inclusion).f (α i) = E'.f i
      exact hiso
    · obtain ⟨β, hβ⟩ := htaut.2
      refine ⟨β, ?_⟩
      intro j
      obtain ⟨iso, hiso⟩ := hβ j
      refine ⟨ObjectProperty.isoMk _ iso, ?_⟩
      apply B.inclusion.map_injective
      show iso.hom ≫ E'.f (β j) = (W.map B.inclusion).f j
      exact hiso
  have hgenE : Sieve.generate Esite.presieve₀ ∈ B.topology Tsite := by
    simpa only [PreZeroHypercover.generate_presieve₀_eq_of_tautologicallyEquivalent
      Esite W htautSite] using hWgen
  have hcoverSite : Esite.sieve₀ ∈ B.topology Tsite := by
    simpa [PreZeroHypercover.sieve₀, PreZeroHypercover.presieve₀] using hgenE
  rw [BigFppfOver.topology, GrothendieckTopology.mem_over_iff,
    Sieve.overEquiv_ofArrows]
  show Esite.sieve₀ ∈ B.topology Tsite
  exact hcoverSite

private theorem affineCoproductData_mono_map_incl
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : BigAffineFppf B S hS} (U : PreZeroHypercover.{u + 1} T) [Finite U.I₀]
    (d : AffineCoproductData B S hS U) (j : Shrink.{u, u + 1} U.I₀) :
    Mono ((BigAffineFppf.inclusion B S hS).map (d.incl j)) := by
  have := isOpenImmersion_map_incl B S hS U d j
  have hleft : Mono ((BigAffineFppf.inclusion B S hS).map (d.incl j)).left := by
    apply B.inclusion.mono_of_mono_map
    show Mono ((BigAffineFppf.toScheme B S hS).map (d.incl j))
    infer_instance
  let : Mono ((BigAffineFppf.inclusion B S hS).map (d.incl j)).left := hleft
  exact Over.mono_of_mono_left ((BigAffineFppf.inclusion B S hS).map (d.incl j))

private theorem respectsIso_of_coprod
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hcoprod : ∀ (n : ℕ)
      (X Y : Fin n → AlgebraicSpaces B S hS)
      (f : ∀ i, X i ⟶ Y i)
      (X₀ Y₀ : AlgebraicSpaces B S hS)
      (ιX : ∀ i, X i ⟶ X₀) (ιY : ∀ i, Y i ⟶ Y₀)
      (g : X₀ ⟶ Y₀),
      IsColimit (Cofan.mk X₀ ιX) → IsColimit (Cofan.mk Y₀ ιY) →
      (∀ i, f i ≫ ιY i = ιX i ≫ g) → (∀ i, P (f i)) → P g) :
    P.RespectsIso := by
  apply MorphismProperty.RespectsIso.mk
  · intro X Y Z e f hf
    let X₁ : Fin 1 → AlgebraicSpaces B S hS := fun _ => Y
    let Y₁ : Fin 1 → AlgebraicSpaces B S hS := fun _ => Z
    let iX : ∀ i : Fin 1, X₁ i ⟶ X := fun _ => e.inv
    let iY : ∀ i : Fin 1, Y₁ i ⟶ Z := fun _ => 𝟙 Z
    exact hcoprod 1 X₁ Y₁ (fun _ => f) X Z iX iY (e.hom ≫ f)
      (Cofan.isColimitMkOfUnique e.symm (Fin 1))
      (Cofan.isColimitMkOfUnique (Iso.refl Z) (Fin 1))
      (by
        intro i
        show f ≫ 𝟙 Z = e.inv ≫ (e.hom ≫ f)
        rw [Category.comp_id, ← Category.assoc, e.inv_hom_id, Category.id_comp])
      (fun _ => hf)
  · intro X Y Z e f hf
    let X₁ : Fin 1 → AlgebraicSpaces B S hS := fun _ => X
    let Y₁ : Fin 1 → AlgebraicSpaces B S hS := fun _ => Y
    let iX : ∀ i : Fin 1, X₁ i ⟶ X := fun _ => 𝟙 X
    let iY : ∀ i : Fin 1, Y₁ i ⟶ Z := fun _ => e.hom
    exact hcoprod 1 X₁ Y₁ (fun _ => f) X Z iX iY (f ≫ e.hom)
      (Cofan.isColimitMkOfUnique (Iso.refl X) (Fin 1))
      (Cofan.isColimitMkOfUnique e (Fin 1))
      (by
        intro i
        show f ≫ e.hom = 𝟙 X ≫ (f ≫ e.hom)
        rw [Category.id_comp])
      (fun _ => hf)

private theorem pullback_snd_comp_iff
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {P : MorphismProperty (AlgebraicSpaces B S hS)} [P.RespectsIso]
    {X Y U W : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (u : U ⟶ Y) (h : W ⟶ U) :
    P (pullback.snd (pullback.snd f u) h) ↔ P (pullback.snd f (h ≫ u)) := by
  let e := pullbackLeftPullbackSndIso f u h
  have he : e.hom ≫ pullback.snd f (h ≫ u) = pullback.snd (pullback.snd f u) h := by
    simp [e]
  rw [← he]
  exact P.cancel_left_of_respectsIso e.hom _

/-- `pullback_snd_comp_iff`, for a base change `c` equal to the composite `h ≫ u`. -/
private theorem pullback_snd_snd_iff_of_comp_eq
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {P : MorphismProperty (AlgebraicSpaces B S hS)} [P.RespectsIso]
    {X Y U W : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (u : U ⟶ Y) (h : W ⟶ U) {c : W ⟶ Y} (hc : h ≫ u = c) :
    P (pullback.snd (pullback.snd f u) h) ↔ P (pullback.snd f c) :=
  hc ▸ pullback_snd_comp_iff f u h

private theorem pullback_mem_of_affine_tests
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {P : MorphismProperty (AlgebraicSpaces B S hS)} [P.RespectsIso]
    (haffine : ∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
      P f ↔ ∀ (T : BigAffineFppf B S hS)
        (g : schemeSpace
          ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y),
        P (pullback.snd f g))
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : P f) : P (pullback.snd f g) :=
  (haffine _).2 fun T h => (pullback_snd_comp_iff (P := P) f g h).mpr ((haffine f).1 hf T (h ≫ g))

private theorem algebraicSpacesToSheaf_preservesPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y Z : AlgebraicSpaces B S hS} (f : X ⟶ Z) (g : Y ⟶ Z) :
    IsPullback
      ((algebraicSpacesToSheaf B S hS).map (pullback.fst f g))
      ((algebraicSpacesToSheaf B S hS).map (pullback.snd f g))
      ((algebraicSpacesToSheaf B S hS).map f)
      ((algebraicSpacesToSheaf B S hS).map g) := by
  let F := algebraicSpacesToSheaf B S hS
  let G := sheafToPresheaf (BigFppfOver.topology B S hS) (Type u)
  let H := F ⋙ G
  let Q := AlgebraicSpaces.fiberProduct B S hS f g
  have hFiber : IsPullback
      (ObjectProperty.homMk (pullback.fst f.hom g.hom) : Q ⟶ X)
      (ObjectProperty.homMk (pullback.snd f.hom g.hom) : Q ⟶ Y) f g :=
    AlgebraicSpaces.isPullback_fiberProduct B S hS f g
  have hMappedFiber : IsPullback
      (H.map (ObjectProperty.homMk (pullback.fst f.hom g.hom) : Q ⟶ X))
      (H.map (ObjectProperty.homMk (pullback.snd f.hom g.hom) : Q ⟶ Y))
      (H.map f) (H.map g) := by
    show IsPullback (pullback.fst f.hom g.hom) (pullback.snd f.hom g.hom) f.hom g.hom
    exact IsPullback.of_hasPullback f.hom g.hom
  have hChosen : IsPullback (pullback.fst f g) (pullback.snd f g) f g :=
    IsPullback.of_hasPullback f g
  let e := hChosen.isoIsPullback _ _ hFiber
  have hMappedChosen : IsPullback
      (H.map (pullback.fst f g)) (H.map (pullback.snd f g)) (H.map f) (H.map g) := by
    apply hMappedFiber.of_iso (H.mapIso e).symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · show H.map (ObjectProperty.homMk (pullback.fst f.hom g.hom)) =
        H.map e.inv ≫ H.map (pullback.fst f g)
      exact congrArg H.map (hChosen.isoIsPullback_inv_fst _ _ hFiber).symm
    · show H.map (ObjectProperty.homMk (pullback.snd f.hom g.hom)) =
        H.map e.inv ≫ H.map (pullback.snd f g)
      exact congrArg H.map (hChosen.isoIsPullback_inv_snd _ _ hFiber).symm
    · simp
    · simp
  exact hMappedChosen.of_map G (by
    show F.map (pullback.fst f g) ≫ F.map f =
      F.map (pullback.snd f g) ≫ F.map g
    rw [← F.map_comp, ← F.map_comp, pullback.condition])

namespace Space

/-- An affine-local morphism property which descends along surjective flat
maps of affine schemes and respects finite coproducts is fpqc local on the
target. -/
@[stacks 041J]
public theorem isLocalAtTarget_fpqc_of_affineDescent
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (P : MorphismProperty (AlgebraicSpaces B S hS))
    (hcoprod : ∀ (n : ℕ)
      (X Y : Fin n → AlgebraicSpaces B S hS)
      (f : ∀ i, X i ⟶ Y i)
      (X₀ Y₀ : AlgebraicSpaces B S hS)
      (ιX : ∀ i, X i ⟶ X₀) (ιY : ∀ i, Y i ⟶ Y₀)
      (g : X₀ ⟶ Y₀),
      IsColimit (Cofan.mk X₀ ιX) →
      IsColimit (Cofan.mk Y₀ ιY) →
      (∀ i, f i ≫ ιY i = ιX i ≫ g) →
      (∀ i, P (f i)) → P g)
    (haffine : ∀ {X Y : AlgebraicSpaces B S hS}
      (f : X ⟶ Y),
      P f ↔ ∀ (T : BigAffineFppf B S hS)
        (g : schemeSpace
          ((BigAffineFppf.inclusion B S hS).obj T) ⟶ Y),
        P (pullback.snd f g))
    (hdescent : ∀ (T T' : BigAffineFppf B S hS)
      (g : T' ⟶ T),
      Flat ((BigAffineFppf.toScheme B S hS).map g) →
      Surjective ((BigAffineFppf.toScheme B S hS).map g) →
      ∀ (X : AlgebraicSpaces B S hS)
        (f : X ⟶ schemeSpace
          ((BigAffineFppf.inclusion B S hS).obj T)),
        P (pullback.snd f
          (schemeSpaceMap
            ((BigAffineFppf.inclusion B S hS).map g))) → P f) :
    P.IsLocalAtTarget (Space.Topology.precoverage.{u, v}
      .fpqc B S hS) := by
  let : P.RespectsIso := respectsIso_of_coprod B S hS P hcoprod
  refine MorphismProperty.IsLocalAtTarget.mk_of_iff (P := P)
    (K := Space.Topology.precoverage.{u, v} .fpqc B S hS) ?_
  intro X Y f R hR
  rcases hR with ⟨I, Yi, gi, rfl, hcover⟩
  rcases hcover with ⟨hY, hYi, hfpqc⟩
  constructor
  · intro hf U k hpb hk
    rcases hk with ⟨i⟩
    exact pullback_mem_of_affine_tests haffine f (gi i) hf
  · intro hlocal
    -- Reduce the assertion to affine tests over the target.
    apply (haffine f).2
    intro T h
    -- Refine this affine test by the finite fpqc family supplied by the covering.
    rcases hfpqc.2 T h.hom with ⟨U, hfin, hU, hfactor⟩
    let : Finite U.I₀ := hfin
    let d := affineCoproductData B S hS U
    let g := d.2
    let inc := BigAffineFppf.inclusion B S hS
    have hpiece (j : Shrink.{u, u + 1} U.I₀) :
        P (pullback.snd f
          ((schemeSpaceMap
            (inc.map (U.f ((equivShrink.{u, u + 1} U.I₀).symm j)))) ≫ h)) := by
      obtain ⟨i, a, hfac⟩ := hfactor ((equivShrink.{u, u + 1} U.I₀).symm j)
      let aj : schemeSpace
          (inc.obj (U.X ((equivShrink.{u, u + 1} U.I₀).symm j))) ⟶ Yi i :=
        ObjectProperty.homMk a
      have hcomp : aj ≫ gi i =
          schemeSpaceMap
            (inc.map (U.f ((equivShrink.{u, u + 1} U.I₀).symm j))) ≫ h := by
        apply ObjectProperty.hom_ext
        exact hfac
      have hnested : P (pullback.snd (pullback.snd f (gi i)) aj) :=
        pullback_mem_of_affine_tests haffine (pullback.snd f (gi i)) aj
          (hlocal (g := gi i) (by exact ⟨i⟩))
      exact (pullback_snd_snd_iff_of_comp_eq (P := P) f (gi i) aj hcomp).mp hnested
    let e := equivShrink.{u, u + 1} U.I₀
    let : Finite (Shrink.{u, u + 1} U.I₀) := Finite.of_equiv U.I₀ e
    let Xsite (j : Shrink.{u, u + 1} U.I₀) :=
      inc.obj (U.X (e.symm j))
    let ιsite (j : Shrink.{u, u + 1} U.I₀) := inc.map (d.incl j)
    have hcover : Sieve.ofArrows Xsite ιsite ∈
        BigFppfOver.topology B S hS (inc.obj d.V) :=
      affineCoproduct_inclusions_cover B S hS U d
    let F (j : Shrink.{u, u + 1} U.I₀) : Scheme.{u} :=
      (BigAffineFppf.toScheme B S hS).obj (U.X (e.symm j))
    have hmono : ∀ j, Mono (ιsite j) := fun j =>
      affineCoproductData_mono_map_incl B S hS U d j
    have hempty : ∀ (Z : BigFppfOver B S hS), IsInitial Z →
        ⊥ ∈ BigFppfOver.topology B S hS Z := by
      intro Z hZ
      exact bottom_mem_bigFppfOver_of_isEmpty B S hS Z
        (isEmpty_bigFppfOver_left_of_isInitial B S hS Z hZ)
    have hdisj : ∀ {i j : Shrink.{u, u + 1} U.I₀} (_hij : i ≠ j)
        {Z : BigFppfOver B S hS} (a : Z ⟶ Xsite i) (b : Z ⟶ Xsite j),
        a ≫ ιsite i = b ≫ ιsite j → Nonempty (IsInitial Z) := by
      intro i j hij Z a b hab
      let toScheme := BigFppfOver.toScheme B S hS
      have hmaps : toScheme.map (a ≫ ιsite i) = toScheme.map (b ≫ ιsite j) :=
        congrArg toScheme.map hab
      have hD (k : Shrink.{u, u + 1} U.I₀) :
          toScheme.map (ιsite k) ≫ d.coprodIso.hom = Sigma.ι F k := by
        show ((BigAffineFppf.toScheme B S hS).map (d.incl k)) ≫
          d.coprodIso.hom = _
        exact d.mapIncl k
      have hsum : toScheme.map a ≫ Sigma.ι F i = toScheme.map b ≫ Sigma.ι F j := by
        calc
          toScheme.map a ≫ Sigma.ι F i =
              (toScheme.map a ≫ toScheme.map (ιsite i)) ≫ d.coprodIso.hom := by
                rw [← hD i]
                simp
          _ = toScheme.map (a ≫ ιsite i) ≫ d.coprodIso.hom := by simp
          _ = toScheme.map (b ≫ ιsite j) ≫ d.coprodIso.hom := by rw [hmaps]
          _ = (toScheme.map b ≫ toScheme.map (ιsite j)) ≫ d.coprodIso.hom := by simp
          _ = toScheme.map b ≫ (toScheme.map (ιsite j) ≫ d.coprodIso.hom) := by simp
          _ = toScheme.map b ≫ Sigma.ι F j := by rw [hD j]
      have hpt (x : (toScheme.obj Z).1) :
          Sigma.ι F i ((toScheme.map a) x) = Sigma.ι F j ((toScheme.map b) x) :=
        congrArg (fun q => q x) hsum
      have hempty : IsEmpty (toScheme.obj Z) := by
        refine ⟨fun x => ?_⟩
        apply hij
        have hval :
            AlgebraicGeometry.sigmaMk F ⟨i, (toScheme.map a) x⟩ =
              AlgebraicGeometry.sigmaMk F ⟨j, (toScheme.map b) x⟩ := by
          simpa only [AlgebraicGeometry.sigmaMk_mk] using hpt x
        exact congrArg Sigma.fst ((AlgebraicGeometry.sigmaMk F).injective hval)
      exact ⟨isInitial_bigFppfOver_of_isEmpty B S hS Z hempty⟩
    let cSite : Cofan (fun j => (inc.obj (U.X (e.symm j))).left) :=
      Cofan.mk (inc.obj d.V).left (fun j => (ιsite j).left)
    have hcSite : IsColimit cSite := by
      let cStd : Cofan F := Cofan.mk (∐ F) (Sigma.ι F)
      let cV : Cofan F := Cofan.mk
        (B.inclusion.obj cSite.pt)
        (fun j => B.inclusion.map (cSite.inj j))
      let eCofan : cV ≅ cStd := Cofan.ext d.coprodIso (by
        intro j
        exact d.mapIncl j)
      have hcV : IsColimit cV :=
        IsColimit.ofIsoColimit (coproductIsCoproduct F) eCofan.symm
      exact isColimitOfReflects B.inclusion
        ((Cofan.isColimitMapCoconeEquiv B.inclusion
          (fun j => (inc.obj (U.X (e.symm j))).left) cSite).symm hcV)
    have hcOver : IsColimit (Cofan.mk (inc.obj d.V) ιsite) := by
      exact isColimitOfReflects (Over.forget (B.obj hS))
        ((Cofan.isColimitMapCoconeEquiv (Over.forget (B.obj hS)) Xsite
          (Cofan.mk (inc.obj d.V) ιsite)).symm hcSite)
    have htarget : IsColimit (Cofan.mk (schemeSpace (inc.obj d.V))
        (fun j => schemeSpaceMap (ιsite j))) :=
      schemeSpaceCofanIsColimit B S hS ιsite hcOver hcover hmono hempty hdisj
    let sheafF := algebraicSpacesToSheaf B S hS
    let targetCofan : Cofan
        (fun j => sheafF.obj (schemeSpace (Xsite j))) :=
      Cofan.mk (sheafF.obj (schemeSpace (inc.obj d.V)))
        (fun j => sheafF.map (schemeSpaceMap (ιsite j)))
    have htargetSheaf : IsColimit targetCofan :=
      schemeSpaceCofanSheafIsColimit B S hS ιsite hcOver hcover hmono hempty hdisj
    let targetSheafFamily : Shrink.{u, u + 1} U.I₀ →
        Sheaf (BigFppfOver.topology B S hS) (Type u) :=
      fun j => sheafF.obj (schemeSpace (Xsite j))
    let : HasColimit (Discrete.functor targetSheafFamily) :=
      HasColimit.mk ⟨targetCofan, htargetSheaf⟩
    have htargetUniversal : IsUniversalColimit targetCofan := by
      let J := BigFppfOver.topology B S hS
      let : J.Subcanonical := bigFppfOver_subcanonical B S hS
      let lift : Sheaf J (Type u) ⥤ Sheaf J (Type (u + 1)) :=
        sheafCompose J (uliftFunctor.{u + 1, u})
      let highCofan : Cofan (fun j => J.uliftYoneda.{u + 1}.obj (Xsite j)) :=
        Cofan.mk (J.uliftYoneda.{u + 1}.obj (inc.obj d.V))
          (fun j => J.uliftYoneda.{u + 1}.map (ιsite j))
      have hHighColimit : IsColimit highCofan := by
        let : ∀ j, Mono (ιsite j) := hmono
        exact isColimitCofanMkUliftYoneda J ιsite hcover hempty hdisj
      have hHighUniversal : IsUniversalColimit highCofan := by
        let : HasSheafify J (Type (u + 1)) := inferInstance
        let : FinitaryPreExtensive (Sheaf J (Type (u + 1))) := inferInstance
        exact FinitaryPreExtensive.isUniversal_finiteCoproducts hHighColimit
      let liftedCocone := lift.mapCocone targetCofan
      let iso (Z : BigFppfOver B S hS) :
          lift.obj ((algebraicSpacesToSheaf B S hS).obj (schemeSpace Z)) ≅
            J.uliftYoneda.{u + 1}.obj Z := by
        let e : J.yoneda.obj Z ≅
            (algebraicSpacesToSheaf B S hS).obj (schemeSpace Z) :=
            ObjectProperty.isoMk _ (Iso.refl _)
        exact (lift.mapIso e.symm) ≪≫ Iso.refl _
      let highFamily (j : Shrink.{u, u + 1} U.I₀) :=
        J.uliftYoneda.{u + 1}.obj (Xsite j)
      let η : Discrete.functor (fun j => lift.obj (targetSheafFamily j)) ≅
          Discrete.functor highFamily :=
        Discrete.natIso (fun j => iso (Xsite j.as))
      let highTransport := (Cocone.precompose η.hom).obj highCofan
      have hHighTransport : IsUniversalColimit highTransport :=
        hHighUniversal.precompose_isIso η.hom
      let δ : (Discrete.functor targetSheafFamily ⋙ lift) ≅
          Discrete.functor (fun j => lift.obj (targetSheafFamily j)) :=
        Discrete.compNatIsoDiscrete targetSheafFamily lift
      let highTransport' := (Cocone.precompose δ.hom).obj highTransport
      have hHighTransport' : IsUniversalColimit highTransport' :=
        hHighTransport.precompose_isIso δ.hom
      let e : liftedCocone ≅ highTransport' := Cocone.ext (iso (inc.obj d.V)) (by
        intro j
        dsimp [highTransport', highTransport, η, δ]
        show lift.map (sheafF.map (schemeSpaceMap (ιsite j.as))) ≫
              lift.map ((ObjectProperty.isoMk _ (Iso.refl _)).symm.hom) =
            lift.map ((ObjectProperty.isoMk _ (Iso.refl _)).symm.hom) ≫
              lift.map (J.yoneda.map (ιsite j.as))
        apply Sheaf.hom_ext
        rfl)
      have hLiftedUniversal : IsUniversalColimit liftedCocone :=
        IsUniversalColimit.of_iso hHighTransport' e.symm
      let fullyFaithfulLift : lift.FullyFaithful :=
        fullyFaithfulSheafCompose J fullyFaithfulULiftFunctor
      have : lift.Full := fullyFaithfulLift.full
      have : lift.Faithful := fullyFaithfulLift.faithful
      have : PreservesLimitsOfShape WalkingCospan lift := by
        have : PreservesLimitsOfShape WalkingCospan
            (lift ⋙ sheafToPresheaf J (Type (u + 1))) := by
          show PreservesLimitsOfShape WalkingCospan
            (sheafToPresheaf J (Type u) ⋙
              (Functor.whiskeringRight _ _ _).obj uliftFunctor.{u + 1, u})
          infer_instance
        exact preservesLimitsOfShape_of_reflects_of_preserves lift
          (sheafToPresheaf J (Type (u + 1)))
      let : ReflectsColimitsOfSize.{u, u} lift := fullyFaithful_reflectsColimits lift
      have : ReflectsColimitsOfShape (Discrete (Shrink.{u, u + 1} U.I₀)) lift :=
        ReflectsColimitsOfSize.reflectsColimitsOfShape
      exact IsUniversalColimit.of_mapCocone lift hLiftedUniversal
    classical
    let : Fintype (Shrink.{u, u + 1} U.I₀) := Fintype.ofFinite _
    let n := Fintype.card (Shrink.{u, u + 1} U.I₀)
    let eFin : Fin n ≃ Shrink.{u, u + 1} U.I₀ :=
      (Fintype.equivFin (Shrink.{u, u + 1} U.I₀)).symm
    let fT := pullback.snd f h
    let u := schemeSpaceMap (inc.map g)
    let total := pullback fT u
    let p := pullback.snd fT u
    let targetIncl (j : Shrink.{u, u + 1} U.I₀) :=
      schemeSpaceMap (ιsite j)
    let sourcePiece (j : Shrink.{u, u + 1} U.I₀) := pullback p (targetIncl j)
    let sourceMap (j : Shrink.{u, u + 1} U.I₀) := pullback.snd p (targetIncl j)
    let sourceCofan : Cofan sourcePiece :=
      Cofan.mk total (fun j => pullback.fst p (targetIncl j))
    let sourceCofanSheaf : Cofan
        (fun j : Shrink.{u, u + 1} U.I₀ => sheafF.obj (sourcePiece j)) :=
      Cofan.mk (sheafF.obj total)
        (fun j => sheafF.map (pullback.fst p (targetIncl j)))
    have hsourceSheaf : IsColimit sourceCofanSheaf := by
      let α : (Discrete.functor (fun j => sheafF.obj (sourcePiece j))) ⟶
          (Discrete.functor targetSheafFamily) :=
        Discrete.natTrans (fun j => sheafF.map (sourceMap j.as))
      have hcomm : α ≫ targetCofan.ι = sourceCofanSheaf.ι ≫
          (Functor.const _).map (sheafF.map p) := by
        ext j x y
        dsimp [α, targetCofan, sourceCofanSheaf, sourceMap, targetIncl]
        show (sheafF.map
              (pullback.snd p (schemeSpaceMap (ιsite j.as)) ≫
                schemeSpaceMap (ιsite j.as))).hom.app x y =
            (sheafF.map
              (pullback.fst p (schemeSpaceMap (ιsite j.as)) ≫ p)).hom.app x y
        exact congrArg (fun k => (sheafF.map k).hom.app x y)
          (pullback.condition (f := p)
            (g := schemeSpaceMap (ιsite j.as))).symm
      have hpb (j : Discrete (Shrink.{u, u + 1} U.I₀)) : IsPullback
          (sheafF.map (pullback.fst p (targetIncl j.as)))
          (sheafF.map (sourceMap j.as)) (sheafF.map p)
          (sheafF.map (targetIncl j.as)) :=
        algebraicSpacesToSheaf_preservesPullback B S hS p (targetIncl j.as)
      exact Classical.choice (htargetUniversal sourceCofanSheaf α (sheafF.map p)
        hcomm (.of_discrete _) (by
          intro j
          simpa [sourceCofanSheaf, targetCofan, α] using hpb j))
    have hsource : IsColimit sourceCofan :=
      isColimit_algebraicSpaces_of_sheaf B S hS (by
        exact (Cofan.isColimitMapCoconeEquiv sheafF sourcePiece sourceCofan).symm
          hsourceSheaf)
    have hpieceForCoprod (j : Shrink.{u, u + 1} U.I₀) : P (sourceMap j) := by
      have hfac : targetIncl j ≫ u =
          schemeSpaceMap
            (inc.map (U.f (e.symm j))) := by
        apply ObjectProperty.hom_ext
        show yoneda.map (inc.map (d.incl j)) ≫ yoneda.map (inc.map g) =
          yoneda.map (inc.map (U.f (e.symm j)))
        rw [← Functor.map_comp, ← Functor.map_comp, d.fac]
      have hbase : P (pullback.snd fT
          (schemeSpaceMap (inc.map (U.f (e.symm j))))) :=
        (pullback_snd_comp_iff (P := P) f h
          (schemeSpaceMap (inc.map (U.f (e.symm j))))).mpr (hpiece j)
      exact (pullback_snd_snd_iff_of_comp_eq (P := P) fT u (targetIncl j) hfac).mpr hbase
    let XFin : Fin n → AlgebraicSpaces B S hS :=
      fun i => sourcePiece (eFin i)
    let YFin : Fin n → AlgebraicSpaces B S hS :=
      fun i => schemeSpace (Xsite (eFin i))
    have hsourceFin : IsColimit (Cofan.mk total
        (fun i => pullback.fst p (targetIncl (eFin i)))) :=
      (Cofan.isColimitEquivOfEquiv (ε := eFin) sourceCofan) hsource
    have htargetFin : IsColimit (Cofan.mk (schemeSpace (inc.obj d.V))
        (fun i => schemeSpaceMap (ιsite (eFin i)))) :=
      (Cofan.isColimitEquivOfEquiv (ε := eFin)
        (Cofan.mk (schemeSpace (inc.obj d.V))
          (fun j => schemeSpaceMap (ιsite j)))) htarget
    have hsum : P p := hcoprod n XFin YFin
      (fun i => sourceMap (eFin i)) total (schemeSpace (inc.obj d.V))
      (fun i => pullback.fst p (targetIncl (eFin i)))
      (fun i => schemeSpaceMap (ιsite (eFin i))) p
      hsourceFin htargetFin
      (by
        intro i
        exact pullback.condition.symm)
      (by
        intro i
        exact hpieceForCoprod (eFin i))
    let Uscheme := U.map (BigAffineFppf.toScheme B S hS)
    have hflatMem : Uscheme.presieve₀ ∈ Scheme.precoverage @Flat
        ((BigAffineFppf.toScheme B S hS).obj T) := by
      show (U.map (BigAffineFppf.toScheme B S hS)).presieve₀ ∈ _
      simpa only [PreZeroHypercover.presieve₀_map, Presieve.map_ofArrows] using hU.2
    have hprops := (Scheme.presieve₀_mem_precoverage_iff Uscheme).mp hflatMem
    have hflatMap : Flat (Sigma.desc fun j =>
        (BigAffineFppf.toScheme B S hS).map (U.f (e.symm j))) := by
      let qShrink := fun j =>
        (BigAffineFppf.toScheme B S hS).map (U.f (e.symm j))
      have hq (j : Shrink.{u, u + 1} U.I₀) : Flat (qShrink j) := by
        exact hprops.2 (e.symm j)
      let : ∀ j : Shrink.{u, u + 1} U.I₀, Flat (qShrink j) := hq
      exact inferInstance
    have hsumMap : d.coprodIso.inv ≫
        (BigAffineFppf.toScheme B S hS).map g =
        Sigma.desc (fun j =>
          (BigAffineFppf.toScheme B S hS).map (U.f (e.symm j))) := by
      apply Sigma.hom_ext
      intro j
      calc
        Sigma.ι F j ≫ d.coprodIso.inv ≫
            (BigAffineFppf.toScheme B S hS).map g =
            ((BigAffineFppf.toScheme B S hS).map (d.incl j) ≫
              d.coprodIso.hom) ≫ d.coprodIso.inv ≫
                (BigAffineFppf.toScheme B S hS).map g := by
                  rw [d.mapIncl j]
        _ = (BigAffineFppf.toScheme B S hS).map (d.incl j) ≫
              (BigAffineFppf.toScheme B S hS).map g := by simp
        _ = (BigAffineFppf.toScheme B S hS).map (U.f (e.symm j)) := by
              rw [← Functor.map_comp, d.fac]
        _ = Sigma.ι F j ≫ Sigma.desc (fun k =>
              (BigAffineFppf.toScheme B S hS).map (U.f (e.symm k))) := by
              rw [Sigma.ι_desc]
    have hgform : (BigAffineFppf.toScheme B S hS).map g =
        d.coprodIso.hom ≫ Sigma.desc (fun j =>
          (BigAffineFppf.toScheme B S hS).map (U.f (e.symm j))) := by
      calc
        (BigAffineFppf.toScheme B S hS).map g =
            𝟙 _ ≫ (BigAffineFppf.toScheme B S hS).map g := by simp
        _ = d.coprodIso.hom ≫ (d.coprodIso.inv ≫
              (BigAffineFppf.toScheme B S hS).map g) := by simp
        _ = _ := by rw [hsumMap]
    have hgFlat : Flat ((BigAffineFppf.toScheme B S hS).map g) := by
      rw [hgform]
      infer_instance
    have hgSurjective : Surjective ((BigAffineFppf.toScheme B S hS).map g) := by
      refine ⟨?_⟩
      intro x
      obtain ⟨j, y, hy⟩ := hprops.1 x
      change U.I₀ at j
      change ((BigAffineFppf.toScheme B S hS).obj (U.X j)).toTopCat at y
      have hj : e.symm (e j) = j := Equiv.symm_apply_apply e j
      have hy' := hy
      change ((BigAffineFppf.toScheme B S hS).map (U.f j)) y = x at hy'
      let y' : ((BigAffineFppf.toScheme B S hS).obj
          (U.X (e.symm (e j)))).1 := by
        exact hj.symm ▸ y
      refine ⟨(BigAffineFppf.toScheme B S hS).map (d.incl (e j)) y', ?_⟩
      calc
        (BigAffineFppf.toScheme B S hS).map g
            ((BigAffineFppf.toScheme B S hS).map (d.incl (e j)) y') =
            (BigAffineFppf.toScheme B S hS).map
              (d.incl (e j) ≫ g) y' := by simp
        _ = (BigAffineFppf.toScheme B S hS).map
              (U.f (e.symm (e j))) y' := by rw [d.fac]
        _ = x := by
          exact (dependent_apply_cast
            (fun k z => (BigAffineFppf.toScheme B S hS).map (U.f k) z)
            hj y).trans hy'
    exact hdescent T d.V g hgFlat hgSurjective (pullback f h)
      (pullback.snd f h) hsum
end Space

end AlgebraicGeometry

end

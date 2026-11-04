module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPullbackStability
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomLimitPreservingReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# The affine case of Stacks 08K4

Let `U` and `T₀` be affine schemes of the site, let `f₀ : U ⟶ T₀`, and let `F`, `G` be
quasi-coherent modules on `U` with `F` of finite presentation.  For an affine test scheme `T`
over `T₀` the base change `U_T = U ×_{T₀} T` is the affine scheme `Spec(A ⊗_R C)`, and the
relative Hom functor `T ↦ Hom_{U_T}(F_T, G_T)` is limit preserving: this is the affine case of
Stacks 08K4, which reduces to Stacks 05LI.

This file reads the relative Hom functor of such a situation on the represented algebraic spaces
of the fibre products `T ×_{T₀} U` taken in the site, and transports to it the colimit
presentation that the descent of morphisms through a limit of affine schemes provides.

## Main definitions

* `AlgebraicGeometry.Space.HomSituation.affineSituation`: the situation of Stacks 08JT whose
  source and base are the algebraic spaces of objects `U`, `T₀` of the site.
* `AlgebraicGeometry.Space.HomSituation.affineTestHom`: the structure morphism of a test scheme,
  as a morphism of the site.
* `AlgebraicGeometry.Space.HomSituation.affineFiber`: the fibre product `T ×_{T₀} U` in the site,
  functorially in the test scheme `T`.
* `AlgebraicGeometry.Space.HomSituation.affineFiberOver`: its represented algebraic space, over
  `U`.

## Main results

* `AlgebraicGeometry.Space.HomSituation.affineFiberOverIso`: the represented algebraic space of
  the fibre product in the site is the base change of algebraic spaces.

## References

* [Stacks Project, Tag 08K4](https://stacks.math.columbia.edu/tag/08K4)
* [Stacks Project, Tag 05LI](https://stacks.math.columbia.edu/tag/05LI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space.HomSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] BigFppfSite.hasPullbacks_schemes

section AffineSituation

variable {U T₀ : BigFppfOver B S hS}

/-- The situation of Stacks 08JT whose source and base are the algebraic spaces of objects `U` and
`T₀` of the site, with structure morphism the image of `f₀ : U ⟶ T₀`. -/
abbrev affineSituation (f₀ : U ⟶ T₀)
    (F G : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
      ((schemeSpaceFunctor B S hS).obj U).2)
    (hFq : F.IsQuasicoherentOnSite) (hGq : G.IsQuasicoherentOnSite) : HomSituation B S hS :=
  HomSituation.mk _ _ ((schemeSpaceFunctor B S hS).map f₀) F G hFq hGq

/-- The structure morphism of a test scheme over the algebraic space of `T₀`, as a morphism of
the site: a Yoneda preimage of the morphism of represented presheaves. -/
def affineTestHom (T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)) : T.left ⟶ T₀ :=
  Classical.choose (⟨_, Yoneda.fullyFaithful.map_preimage
    (show yoneda.obj T.left ⟶ yoneda.obj T₀ from T.hom.hom)⟩ :
      ∃ t : T.left ⟶ T₀, yoneda.map t = T.hom.hom)

/-- The image of `affineTestHom T` under the Yoneda embedding is the structure morphism of `T`. -/
theorem yoneda_map_affineTestHom (T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)) :
    yoneda.map (affineTestHom T) = T.hom.hom :=
  Classical.choose_spec (⟨_, Yoneda.fullyFaithful.map_preimage
    (show yoneda.obj T.left ⟶ yoneda.obj T₀ from T.hom.hom)⟩ :
      ∃ t : T.left ⟶ T₀, yoneda.map t = T.hom.hom)

/-- The structure morphisms `affineTestHom` are compatible with morphisms of test schemes. -/
theorem affineTestHom_comp {T' T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)}
    (g : T' ⟶ T) : g.left ≫ affineTestHom T = affineTestHom T' := by
  refine Yoneda.fullyFaithful.map_injective ?_
  rw [Functor.map_comp, yoneda_map_affineTestHom, yoneda_map_affineTestHom]
  exact congrArg (fun k ↦ k.hom) (CostructuredArrow.w g)

variable (f₀ : U ⟶ T₀)

/-- The morphism `T' ×_{T₀} U ⟶ T ×_{T₀} U` of fibre products in the site induced by a morphism
`T' ⟶ T` of test schemes. -/
def affineFiberMap {T' T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)}
    (g : T' ⟶ T) : pullback (affineTestHom T') f₀ ⟶ pullback (affineTestHom T) f₀ :=
  pullback.lift (pullback.fst _ _ ≫ g.left) (pullback.snd _ _) (by
    rw [Category.assoc, affineTestHom_comp, pullback.condition])

/-- The first projection of `affineFiberMap f₀ g` is induced by `g`. -/
@[reassoc (attr := simp)]
theorem affineFiberMap_fst {T' T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)}
    (g : T' ⟶ T) : affineFiberMap f₀ g ≫ pullback.fst _ _ = pullback.fst _ _ ≫ g.left :=
  pullback.lift_fst _ _ _

/-- The morphism `affineFiberMap f₀ g` commutes with the second projections to `U`. -/
@[reassoc (attr := simp)]
theorem affineFiberMap_snd {T' T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)}
    (g : T' ⟶ T) : affineFiberMap f₀ g ≫ pullback.snd _ _ = pullback.snd _ _ :=
  pullback.lift_snd _ _ _

/-- The morphism `affineFiberMap f₀` of the identity is the identity. -/
theorem affineFiberMap_id (T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)) :
    affineFiberMap f₀ (𝟙 T) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp

/-- The morphism `affineFiberMap f₀` of a composite is the composite of the morphisms. -/
theorem affineFiberMap_comp {T'' T' T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)}
    (g : T'' ⟶ T') (h : T' ⟶ T) :
    affineFiberMap f₀ (g ≫ h) = affineFiberMap f₀ g ≫ affineFiberMap f₀ h := by
  apply pullback.hom_ext
  · rw [affineFiberMap_fst, Category.assoc, affineFiberMap_fst, affineFiberMap_fst_assoc]
    rfl
  · rw [affineFiberMap_snd, Category.assoc, affineFiberMap_snd, affineFiberMap_snd]

/-- **The fibre product `T ×_{T₀} U` in the site**, functorially in the test scheme `T`. -/
abbrev affineFiber :
    Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀) ⥤ BigFppfOver B S hS where
  obj T := pullback (affineTestHom T) f₀
  map g := affineFiberMap f₀ g
  map_id T := affineFiberMap_id f₀ T
  map_comp g h := affineFiberMap_comp f₀ g h

/-- **The represented algebraic space of `T ×_{T₀} U`, over `U`**, functorially in the test
scheme `T`. -/
abbrev affineFiberOver :
    Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀) ⥤
      Over ((schemeSpaceFunctor B S hS).obj U) where
  obj T := Over.mk ((schemeSpaceFunctor B S hS).map (pullback.snd (affineTestHom T) f₀))
  map g := Over.homMk ((schemeSpaceFunctor B S hS).map (affineFiberMap f₀ g))
    ((Functor.map_comp _ _ _).symm.trans (congrArg _ (affineFiberMap_snd f₀ g)))
  map_id T := by
    ext1
    exact (congrArg (schemeSpaceFunctor B S hS).map (affineFiberMap_id f₀ T)).trans
      (CategoryTheory.Functor.map_id (schemeSpaceFunctor B S hS) _)
  map_comp g h := by
    ext1
    exact (congrArg (schemeSpaceFunctor B S hS).map (affineFiberMap_comp f₀ g h)).trans
      (Functor.map_comp (schemeSpaceFunctor B S hS) _ _)

/-- The represented square of the fibre product in the site is cartesian among presheaves. -/
theorem isPullback_affineFiber (T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)) :
    IsPullback (yoneda.map (pullback.snd (affineTestHom T) f₀))
      (yoneda.map (pullback.fst (affineTestHom T) f₀)) (yoneda.map f₀) T.hom.hom := by
  have h := ((IsPullback.of_hasPullback (affineTestHom T) f₀).flip).map yoneda
  rwa [yoneda_map_affineTestHom] at h

/-- The represented algebraic space of `T ×_{T₀} U` is the base change `X_T`. -/
def affineFiberIso (T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)) :
    (schemeSpaceFunctor B S hS).obj (pullback (affineTestHom T) f₀) ≅
      baseChangeSpace ((schemeSpaceFunctor B S hS).map f₀) T :=
  ObjectProperty.isoMk _ (isPullback_affineFiber f₀ T).isoPullback

/-- The isomorphism `affineFiberIso f₀ T` intertwines the projection of the base change to the
source with the second projection of the fibre product in the site. -/
@[reassoc (attr := simp)]
theorem affineFiberIso_hom_projection
    (T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)) :
    (affineFiberIso f₀ T).hom ≫ baseChangeProjection ((schemeSpaceFunctor B S hS).map f₀) T =
      (schemeSpaceFunctor B S hS).map (pullback.snd (affineTestHom T) f₀) :=
  ObjectProperty.hom_ext _ ((isPullback_affineFiber f₀ T).isoPullback_hom_fst)

/-- The isomorphism `affineFiberIso f₀ T` intertwines the morphism of the base change to `T`
with the first projection of the fibre product in the site. -/
@[reassoc (attr := simp)]
theorem affineFiberIso_hom_inclusion
    (T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)) :
    (affineFiberIso f₀ T).hom ≫ baseChangeInclusion ((schemeSpaceFunctor B S hS).map f₀) T =
      (schemeSpaceFunctor B S hS).map (pullback.fst (affineTestHom T) f₀) :=
  ObjectProperty.hom_ext _ ((isPullback_affineFiber f₀ T).isoPullback_hom_snd)

/-- **The base change along the test schemes is the represented fibre product in the site.** -/
def affineFiberOverIso :
    affineFiberOver f₀ ≅ baseChangeOver ((schemeSpaceFunctor B S hS).map f₀) :=
  NatIso.ofComponents
    (fun T ↦ Over.isoMk (show ((affineFiberOver f₀).obj T).left ≅
      ((baseChangeOver ((schemeSpaceFunctor B S hS).map f₀)).obj T).left from affineFiberIso f₀ T)
      (affineFiberIso_hom_projection f₀ T))
    (fun {T' T} g ↦ by
      refine Over.OverMorphism.ext (baseChange_hom_ext ((schemeSpaceFunctor B S hS).map f₀) ?_ ?_)
      · change ((schemeSpaceFunctor B S hS).map (affineFiberMap f₀ g) ≫
            (affineFiberIso f₀ T).hom) ≫ _ = ((affineFiberIso f₀ T').hom ≫ baseChangeMap _ g) ≫ _
        simp only [Category.assoc, affineFiberIso_hom_projection, baseChangeMap_comp_projection]
        rw [← Functor.map_comp, affineFiberMap_snd]
      · change ((schemeSpaceFunctor B S hS).map (affineFiberMap f₀ g) ≫
            (affineFiberIso f₀ T).hom) ≫ _ = ((affineFiberIso f₀ T').hom ≫ baseChangeMap _ g) ≫ _
        simp only [Category.assoc, affineFiberIso_hom_inclusion, baseChangeMap_comp_inclusion,
          affineFiberIso_hom_inclusion_assoc]
        rw [← Functor.map_comp, ← Functor.map_comp, affineFiberMap_fst])

/-- **The relative Hom functor of an affine situation, read on the represented fibre products.** -/
def affineHomFunctorIso
    (F G : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
      ((schemeSpaceFunctor B S hS).obj U).2)
    (hFq : F.IsQuasicoherentOnSite) (hGq : G.IsQuasicoherentOnSite) :
    (affineFiberOver f₀).op ⋙ moduleHomOver (modulePushforwardCoherence B S hS) F G ≅
      (affineSituation f₀ F G hFq hGq).homFunctor (modulePushforwardCoherence B S hS) :=
  Functor.isoWhiskerRight (NatIso.op (affineFiberOverIso f₀)).symm
    (moduleHomOver (modulePushforwardCoherence B S hS) F G)

end AffineSituation

/-! ### The fibre products along a limit of test schemes -/

section Limit

/-- **Base change along a fixed morphism preserves a cofiltered limit.**  Let `c` be a limit cone
on a cofiltered diagram `D` over `T`, let `φ : Y ⟶ T`, and let `c'` be a cone on a diagram `D'`
whose members are fibre products `D j ×_T Y`, compatibly with the transition maps, with vertex
the fibre product `c.pt ×_T Y`.  Then `c'` is a limit cone: a cone over `D'` gives a cone over `D`
through the first projections, and its lift together with the second projection, which does not
depend on the index, lifts into the fibre product of the vertex. -/
def isLimitOfIsPullbackOfIsLimit {C : Type*} [Category C] {J : Type*} [Category J]
    [IsCofiltered J] {D D' : J ⥤ C} {c : Cone D} (hc : IsLimit c) (c' : Cone D') {Y T : C}
    (φ : Y ⟶ T) (τ : ∀ j, D.obj j ⟶ T) (p : ∀ j, D'.obj j ⟶ D.obj j)
    (hp : ∀ {j k} (e : j ⟶ k), D'.map e ≫ p k = p j ≫ D.map e) (q : ∀ j, D'.obj j ⟶ Y)
    (hq : ∀ {j k} (e : j ⟶ k), D'.map e ≫ q k = q j)
    (hsq : ∀ j, IsPullback (p j) (q j) (τ j) φ)
    (pc : c'.pt ⟶ c.pt) (hpc : ∀ j, c'.π.app j ≫ p j = pc ≫ c.π.app j)
    (qc : c'.pt ⟶ Y) (hqc : ∀ j, c'.π.app j ≫ q j = qc)
    (τc : c.pt ⟶ T) (hτc : ∀ j, c.π.app j ≫ τ j = τc)
    (hsqc : IsPullback pc qc τc φ) : IsLimit c' := by
  let j₀ : J := (IsCofiltered.nonempty : Nonempty J).some
  have hsnd : ∀ (s : Cone D') (j : J), s.π.app j ≫ q j = s.π.app j₀ ≫ q j₀ := by
    intro s j
    have key : ∀ (k j : J) (e : k ⟶ j), s.π.app j ≫ q j = s.π.app k ≫ q k := fun k j e ↦ by
      rw [← s.w e, Category.assoc, hq e]
    rw [key (IsCofiltered.min j j₀) j (IsCofiltered.minToLeft j j₀),
      key (IsCofiltered.min j j₀) j₀ (IsCofiltered.minToRight j j₀)]
  let first : Cone D' → Cone D := fun s ↦
    { pt := s.pt
      π :=
        { app j := s.π.app j ≫ p j
          naturality j k e := by
            simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
              Category.assoc]
            rw [← hp e, ← Category.assoc, s.w e] } }
  have hcond : ∀ s : Cone D', hc.lift (first s) ≫ τc = (s.π.app j₀ ≫ q j₀) ≫ φ := by
    intro s
    rw [← hτc j₀, ← Category.assoc, hc.fac (first s) j₀, Category.assoc, Category.assoc,
      (hsq j₀).w]
  refine
    { lift := fun s ↦ hsqc.lift (hc.lift (first s)) (s.π.app j₀ ≫ q j₀) (hcond s)
      fac := fun s j ↦ (hsq j).hom_ext ?_ ?_
      uniq := fun s m hm ↦ hsqc.hom_ext ?_ ?_ }
  · rw [Category.assoc, hpc, ← Category.assoc, hsqc.lift_fst]
    exact hc.fac (first s) j
  · rw [Category.assoc, hqc, hsqc.lift_snd, hsnd s j]
  · rw [hsqc.lift_fst]
    refine hc.uniq (first s) _ fun j ↦ ?_
    change (m ≫ pc) ≫ c.π.app j = s.π.app j ≫ p j
    rw [Category.assoc, ← hpc, ← Category.assoc, hm j]
  · rw [hsqc.lift_snd, ← hm j₀, Category.assoc, hqc]

attribute [local instance] preservesLimitsOfShape_walkingCospan_toScheme

variable {U T₀ : BigFppfOver B S hS} (f₀ : U ⟶ T₀)
  {I : Type u} [Category.{u} I] [IsCofiltered I]
  {E : I ⥤ Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)} (c : Cone E)

/-- **Base change along `f₀` preserves a cofiltered limit of test schemes.**  If the underlying
schemes of `c` form a limit, so do the underlying schemes of the fibre products `E i ×_{T₀} U`,
the functor to schemes preserving fibre products. -/
def isLimitAffineFiberMapCone
    (hc : IsLimit ((CostructuredArrow.proj (schemeSpaceFunctor B S hS)
      ((schemeSpaceFunctor B S hS).obj T₀) ⋙ BigFppfOver.toScheme B S hS).mapCone c)) :
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone ((affineFiber f₀).mapCone c)) := by
  let Φ := BigFppfOver.toScheme B S hS
  have hP : ∀ T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀),
      IsPullback (Φ.map (pullback.fst (affineTestHom T) f₀))
        (Φ.map (pullback.snd (affineTestHom T) f₀)) (Φ.map (affineTestHom T)) (Φ.map f₀) :=
    fun T ↦ (IsPullback.of_hasPullback (affineTestHom T) f₀).map Φ
  exact isLimitOfIsPullbackOfIsLimit hc _ (Φ.map f₀) (fun j ↦ Φ.map (affineTestHom (E.obj j)))
    (fun j ↦ Φ.map (pullback.fst (affineTestHom (E.obj j)) f₀))
    (fun e ↦ (Φ.map_comp _ _).symm.trans ((congrArg Φ.map (affineFiberMap_fst f₀ (E.map e))).trans
      (Φ.map_comp _ _)))
    (fun j ↦ Φ.map (pullback.snd (affineTestHom (E.obj j)) f₀))
    (fun e ↦ (Φ.map_comp _ _).symm.trans (congrArg Φ.map (affineFiberMap_snd f₀ (E.map e))))
    (fun j ↦ hP (E.obj j))
    (Φ.map (pullback.fst (affineTestHom c.pt) f₀))
    (fun j ↦ (Φ.map_comp _ _).symm.trans ((congrArg Φ.map (affineFiberMap_fst f₀ (c.π.app j))).trans
      (Φ.map_comp _ _)))
    (Φ.map (pullback.snd (affineTestHom c.pt) f₀))
    (fun j ↦ (Φ.map_comp _ _).symm.trans (congrArg Φ.map (affineFiberMap_snd f₀ (c.π.app j))))
    (Φ.map (affineTestHom c.pt))
    (fun j ↦ (Φ.map_comp _ _).symm.trans (congrArg Φ.map (affineTestHom_comp (c.π.app j))))
    (hP c.pt)

end Limit

/-! ### The colimit of Hom sets along the stages over a chosen stage -/

section HomColimit

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (V : I ⥤ BigFppfOver B S hS)
  (c : Cone V) (k : I)
  (M N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj (V.obj k)).1
    ((schemeSpaceFunctor B S hS).obj (V.obj k)).2)

omit [IsCofiltered I] in
/-- The commutation of the image of the cone `c` with the transition morphisms, in the
represented algebraic spaces. -/
theorem schemeSpaceFunctor_map_cone_w {j : I} (e : j ⟶ k) :
    (schemeSpaceFunctor B S hS).map (c.π.app j) ≫ (schemeSpaceFunctor B S hS).map (V.map e) =
      (schemeSpaceFunctor B S hS).map (c.π.app k) :=
  (Functor.map_comp _ _ _).symm.trans (congrArg _ (c.w e))

/-- The cone `c` read over the stage `k`, in the represented algebraic spaces: the vertex is the
represented space of `c.pt` over that of `V k` through `c.π k`, and the legs are the represented
projections. -/
def stageSpaceCone :
    Cone (Over.post V ⋙ Over.post (schemeSpaceFunctor B S hS) :
      Over k ⥤ Over ((schemeSpaceFunctor B S hS).obj (V.obj k))) where
  pt := Over.mk ((schemeSpaceFunctor B S hS).map (c.π.app k))
  π :=
    { app A := Over.homMk ((schemeSpaceFunctor B S hS).map (c.π.app A.left))
        (schemeSpaceFunctor_map_cone_w V c k A.hom)
      naturality A A' g := by
        ext1
        change 𝟙 _ ≫ (schemeSpaceFunctor B S hS).map (c.π.app A'.left) =
          (schemeSpaceFunctor B S hS).map (c.π.app A.left) ≫
            (schemeSpaceFunctor B S hS).map (V.map g.left)
        rw [Category.id_comp, ← Functor.map_comp, c.w g.left] }

/-- The action of `moduleHomOver` on a morphism of algebraic spaces over `X`, applied to a
homomorphism: conjugation by the comparison of inverse images. -/
theorem moduleHomOver_map_apply {X : AlgebraicSpaces B S hS}
    (F G : Modules.{u, u} B S hS X.1 X.2) {Z Z' : (Over X)ᵒᵖ} (m : Z ⟶ Z')
    (α : (moduleHomOver (modulePushforwardCoherence B S hS) F G).obj Z) :
    (moduleHomOver (modulePushforwardCoherence B S hS) F G).map m α =
      Functor.conjHom (modulePullbackTriangle B S hS (Over.w m.unop)) α := by
  rw [moduleHomOver_map]
  exact TypeCat.ofHom_apply _ _

omit [IsCofiltered I] in
/-- The restriction from a stage over `k` to the vertex is conjugation by the comparison of
inverse images along `c.π j` and `V.map e`. -/
theorem moduleHomOver_map_stageSpaceCone {j : I} (e : j ⟶ k)
    (φ' : (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e))).obj M ⟶
      (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e))).obj N) :
    (moduleHomOver (modulePushforwardCoherence B S hS) M N).map
        ((stageSpaceCone V c k).π.app (Over.mk e)).op φ' =
      Functor.conjHom (modulePullbackTriangle B S hS (schemeSpaceFunctor_map_cone_w V c k e))
        φ' := by
  rw [moduleHomOver_map]
  exact TypeCat.ofHom_apply _ _

omit [IsCofiltered I] in
/-- The transition from a stage `e : j ⟶ k` to a later stage `e' ≫ e` is conjugation by the
comparison of inverse images along `V.map e'` and `V.map e`. -/
theorem moduleHomOver_map_stageTransition {j j' : I} (e : j ⟶ k) (e' : j' ⟶ j)
    (α : (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e))).obj M ⟶
      (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e))).obj N) :
    (moduleHomOver (modulePushforwardCoherence B S hS) M N).map
        ((Over.post V ⋙ Over.post (schemeSpaceFunctor B S hS)).map
          (Over.homMk e' rfl : Over.mk (e' ≫ e) ⟶ Over.mk e)).op α =
      Functor.conjHom (modulePullbackTriangle B S hS
        (show (schemeSpaceFunctor B S hS).map (V.map e') ≫
            (schemeSpaceFunctor B S hS).map (V.map e) =
          (schemeSpaceFunctor B S hS).map (V.map (e' ≫ e)) by
          rw [← Functor.map_comp, ← Functor.map_comp])) α := by
  rw [moduleHomOver_map]
  exact TypeCat.ofHom_apply _ _

/-- Conjugation by an isomorphism of functors is injective on the morphisms it conjugates. -/
theorem map_eq_of_conjHom_eq' {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N : C}
    {α β : P₁.obj M ⟶ P₁.obj N} (h : Functor.conjHom e α = Functor.conjHom e β) :
    L.map α = L.map β := by
  unfold Functor.conjHom at h
  rwa [cancel_epi, cancel_mono] at h

/-- **The Hom sets of the inverse images along the stages over `k` have the Hom set of the
inverse images to the vertex as their colimit**, provided the descent of morphisms through the
limit (`hfull`) and the eventual equality of morphisms (`hfaith`) hold for `M` and `N`. -/
theorem nonempty_isColimit_moduleHomOver_conePost
    (hfull : ∀ φ : (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (c.π.app k))).obj M ⟶
        (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (c.π.app k))).obj N,
      ∃ (j : I) (e : j ⟶ k)
        (φ' : (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e))).obj M ⟶
          (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e))).obj N),
        Functor.conjHom (modulePullbackTriangle B S hS (schemeSpaceFunctor_map_cone_w V c k e))
          φ' = φ)
    (hfaith : ∀ (j : I) (e : j ⟶ k)
        (φ ψ : (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e))).obj M ⟶
          (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e))).obj N),
        (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (c.π.app j))).map φ =
          (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (c.π.app j))).map ψ →
        ∃ (j' : I) (e' : j' ⟶ j),
          (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e'))).map φ =
            (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e'))).map ψ) :
    Nonempty (IsColimit ((moduleHomOver (modulePushforwardCoherence B S hS) M N).mapCocone
      (stageSpaceCone V c k).op)) := by
  refine nonempty_isColimit_mapCocone_of_exists_of_eventually_eq _ _ _ ?_ ?_
  · intro x
    obtain ⟨j, e, φ', hφ'⟩ := hfull x
    exact ⟨Over.mk e, φ', (moduleHomOver_map_stageSpaceCone V c k M N e φ').trans hφ'⟩
  · intro A φ ψ hφψ
    rw [moduleHomOver_map_apply, moduleHomOver_map_apply] at hφψ
    obtain ⟨j', e', he'⟩ := hfaith A.left A.hom φ ψ (map_eq_of_conjHom_eq' _ hφψ)
    refine ⟨Over.mk (e' ≫ A.hom), Over.homMk e' rfl, ?_⟩
    rw [moduleHomOver_map_stageTransition V k M N A.hom e' φ,
      moduleHomOver_map_stageTransition V k M N A.hom e' ψ]
    unfold Functor.conjHom
    rw [he']

end HomColimit

/-! ### The affine case -/

section AffineCase

attribute [local instance] preservesLimitsOfShape_walkingCospan_toScheme

/-- **The descent of morphisms through a cofiltered limit of affine schemes, on their represented
algebraic spaces, into a quasi-coherent module**: the two clauses of Stacks 01ZR (2), (3) — read
on the small étale sites of the algebraic spaces represented by an inverse system of affine
schemes of the site — for a source module of finite presentation and a quasi-coherent target. -/
def AffineSpaceHomDescent (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) : Prop :=
  ∀ {I : Type u} [Category.{u} I] [IsCofiltered I] (V : I ⥤ BigFppfOver B S hS) (c : Cone V),
    IsLimit ((BigFppfOver.toScheme B S hS).mapCone c) →
    (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V.obj i))) →
    IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt) →
    ∀ (k : I) (M N : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj (V.obj k)).1
      ((schemeSpaceFunctor B S hS).obj (V.obj k)).2),
      M.IsFinitePresentationOnSite → N.IsQuasicoherentOnSite →
      (∀ φ : (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (c.π.app k))).obj M ⟶
          (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (c.π.app k))).obj N,
        ∃ (j : I) (e : j ⟶ k)
          (φ' : (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e))).obj M ⟶
            (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e))).obj N),
          Functor.conjHom (modulePullbackTriangle B S hS (schemeSpaceFunctor_map_cone_w V c k e))
            φ' = φ) ∧
      (∀ (j : I) (e : j ⟶ k)
          (φ ψ : (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e))).obj M ⟶
            (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e))).obj N),
          (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (c.π.app j))).map φ =
            (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (c.π.app j))).map ψ →
          ∃ (j' : I) (e' : j' ⟶ j),
            (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e'))).map φ =
              (modulePullback B S hS ((schemeSpaceFunctor B S hS).map (V.map e'))).map ψ)

variable {U T₀ : BigFppfOver B S hS} (f₀ : U ⟶ T₀)
  (F G : Modules.{u, u} B S hS ((schemeSpaceFunctor B S hS).obj U).1
    ((schemeSpaceFunctor B S hS).obj U).2)
  (hFq : F.IsQuasicoherentOnSite) (hGq : G.IsQuasicoherentOnSite)

/-- The fibre product of affine schemes over an affine scheme in the site is affine. -/
theorem isAffine_affineFiber (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (T : Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀))
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T.left)) :
    IsAffine ((BigFppfOver.toScheme B S hS).obj ((affineFiber f₀).obj T)) := by
  have := hU
  have := hT₀
  have := hT
  exact @IsAffine.of_isIso _ _ (PreservesPullback.iso (BigFppfOver.toScheme B S hS)
    (affineTestHom T) f₀).hom (Iso.isIso_hom _) inferInstance

variable {f₀} in
/-- Over a chosen stage `k`, the stages of the represented fibre products read over `U` through
the stage's projection are the represented fibre products themselves. -/
def stageFiberIso {I : Type u} [Category.{u} I]
    (E : I ⥤ Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)) (k : I)
    (q : (schemeSpaceFunctor B S hS).obj (pullback (affineTestHom (E.obj k)) f₀) ⟶
      (schemeSpaceFunctor B S hS).obj U)
    (hq : q = (schemeSpaceFunctor B S hS).map (pullback.snd (affineTestHom (E.obj k)) f₀)) :
    (Over.post (E ⋙ affineFiber f₀) ⋙ Over.post (schemeSpaceFunctor B S hS)) ⋙ Over.map q ≅
      Over.forget k ⋙ E ⋙ affineFiberOver f₀ :=
  NatIso.ofComponents (fun A ↦ Over.isoMk (Iso.refl _) (by
      subst hq
      change 𝟙 _ ≫ (schemeSpaceFunctor B S hS).map (pullback.snd _ _) =
        (schemeSpaceFunctor B S hS).map (affineFiberMap f₀ (E.map A.hom)) ≫
          (schemeSpaceFunctor B S hS).map (pullback.snd _ _)
      rw [Category.id_comp, ← Functor.map_comp, affineFiberMap_snd]))
    (fun {A A'} g ↦ by
      ext1
      change (schemeSpaceFunctor B S hS).map (affineFiberMap f₀ (E.map g.left)) ≫ 𝟙 _ =
        𝟙 _ ≫ (schemeSpaceFunctor B S hS).map (affineFiberMap f₀ (E.map g.left))
      rw [Category.id_comp, Category.comp_id])

variable {f₀} in
/-- Over a chosen stage `k`, the vertex of the represented fibre products read over `U` through
the stage's projection is the represented fibre product of the vertex. -/
def vertexFiberIso {I : Type u} [Category.{u} I] [IsCofiltered I]
    {E : I ⥤ Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)} (c : Cone E) (k : I)
    (q : (schemeSpaceFunctor B S hS).obj (pullback (affineTestHom (E.obj k)) f₀) ⟶
      (schemeSpaceFunctor B S hS).obj U)
    (hq : q = (schemeSpaceFunctor B S hS).map (pullback.snd (affineTestHom (E.obj k)) f₀)) :
    (Over.map q).obj (stageSpaceCone (E ⋙ affineFiber f₀) ((affineFiber f₀).mapCone c) k).pt ≅
      (affineFiberOver f₀).obj c.pt :=
  Over.isoMk (Iso.refl _) (by
    subst hq
    change 𝟙 _ ≫ (schemeSpaceFunctor B S hS).map (pullback.snd _ _) =
      (schemeSpaceFunctor B S hS).map (affineFiberMap f₀ (c.π.app k)) ≫
        (schemeSpaceFunctor B S hS).map (pullback.snd _ _)
    rw [Category.id_comp, ← Functor.map_comp, affineFiberMap_snd])

variable {f₀} in
/-- The isomorphism `vertexFiberIso` is compatible with the cone projections, through the
isomorphisms `stageFiberIso` of the stages. -/
theorem vertexFiberIso_compat {I : Type u} [Category.{u} I] [IsCofiltered I]
    {E : I ⥤ Space.SchemesOver ((schemeSpaceFunctor B S hS).obj T₀)} (c : Cone E) (k : I)
    (q : (schemeSpaceFunctor B S hS).obj (pullback (affineTestHom (E.obj k)) f₀) ⟶
      (schemeSpaceFunctor B S hS).obj U)
    (hq : q = (schemeSpaceFunctor B S hS).map (pullback.snd (affineTestHom (E.obj k)) f₀))
    (A : Over k) :
    (Over.map q).map
        ((stageSpaceCone (E ⋙ affineFiber f₀) ((affineFiber f₀).mapCone c) k).π.app A) ≫
          (stageFiberIso E k q hq).hom.app A =
      (vertexFiberIso c k q hq).hom ≫ ((affineFiberOver f₀).mapCone c).π.app A.left := by
  ext1
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **The affine case of Stacks 08K4, from the descent of morphisms through limits of affine
schemes.**  For affine `U` and `T₀` and a source module of finite presentation, the relative Hom
functor of the affine situation is limit preserving. -/
theorem limitPreserving_affineSituation_of_affineSpaceHomDescent
    (hdesc : AffineSpaceHomDescent B S hS)
    (hU : IsAffine ((BigFppfOver.toScheme B S hS).obj U))
    (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (hF : F.IsFinitePresentationOnSite) :
    LimitPreserving.{u, u + 1, u, u} (affineSituation f₀ F G hFq hGq).testSchemeFunctor
      ((affineSituation f₀ F G hFq hGq).homFunctor (modulePushforwardCoherence B S hS)) := by
  refine limitPreserving_of_natIso (affineHomFunctorIso f₀ F G hFq hGq) ?_
  intro I _ _ E c hc hE hpt
  let k : I := (IsCofiltered.nonempty : Nonempty I).some
  have hcV := isLimitAffineFiberMapCone f₀ c hc
  have hM := isFinitePresentationOnSite_modulePullback B S hS
    ((schemeSpaceFunctor B S hS).map (pullback.snd (affineTestHom (E.obj k)) f₀)) F hF
  have hN := isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS
    ((schemeSpaceFunctor B S hS).map (pullback.snd (affineTestHom (E.obj k)) f₀)) G hGq
  obtain ⟨hfull, hfaith⟩ := hdesc (E ⋙ affineFiber f₀) ((affineFiber f₀).mapCone c) hcV
    (fun i ↦ isAffine_affineFiber f₀ hU hT₀ _ (hE i)) (isAffine_affineFiber f₀ hU hT₀ _ hpt) k _ _
    hM hN
  obtain ⟨hcol⟩ := nonempty_isColimit_moduleHomOver_conePost _ _ k _ _ hfull hfaith
  exact nonempty_isColimit_mapCocone_of_overStage _
    (moduleHomOverPullback (modulePushforwardCoherence B S hS) _ F G) (E ⋙ affineFiberOver f₀)
    ((affineFiberOver f₀).mapCone c) k _ _ (stageFiberIso E k _ rfl) (vertexFiberIso c k _ rfl)
    (vertexFiberIso_compat c k _ rfl) hcol

end AffineCase

end AlgebraicGeometry.Space.HomSituation

end

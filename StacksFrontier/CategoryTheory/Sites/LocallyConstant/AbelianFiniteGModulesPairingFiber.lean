module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.AbelianFiniteGModulesPairing

/-!
# Pairings of finite locally constant abelian sheaves on fibres

Let `e` be an equivalence between the finite locally constant sheaves of sets on a site and the
finite continuous `G`-sets, and `ω` a functor on sheaves of sets (a fibre functor, for instance
the stalk at a geometric point) together with an identification `σ` of `ω` on finite locally
constant sheaves with the underlying set of `e`. A morphism `ψ : A × B → T` of finite
continuous `G`-sets which is given on elements by a map of sets `f` is carried by `e⁻¹` to a
morphism of sheaves `e⁻¹A × e⁻¹B → e⁻¹T`, and `σ` (followed by the counit of `e`) identifies `ω`
of it with `f`. Applied to the pairing of finite locally constant abelian sheaves attached to an
equivariant biadditive map `P : M × N → L` of finite discrete `G`-modules
(`Stacks.ConstantSheaf.finiteLocallyConstantInternalPairing`) this shows that on fibres the
pairing is `P`; this is how the perfectness of the pairing of coefficients
`ℱ_ρ ⊗ ℱ_{ρ^∨} → ℤ/ℓ^kℤ` of the purity half of
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH) is tested on stalks.

## Main definitions

* `Stacks.ConstantSheaf.fiberCounit`: `ω(e⁻¹A) → A`, the identification `σ` followed by the counit
  of `e`.
* `Stacks.ConstantSheaf.finiteGModuleCommGrpCounit`: the underlying morphism of `G`-sets of the
  counit of `CategoryTheory.commGrpContinuousGSetEquivalence`.

## Main results

* `CategoryTheory.IsPairingBy`: a morphism out of a cartesian product given on elements by a map.
* `Stacks.ConstantSheaf.finiteGModuleCommGrpCounit_finiteGModulePairing`: the internal pairing of
  finite `G`-sets attached to `P` is `P` on elements.
* `Stacks.ConstantSheaf.fiberCounit_map_pairing`: `ω` of the morphism `e⁻¹A × e⁻¹B → e⁻¹T` of
  `ψ` is `f` under `fiberCounit`.
* `Stacks.ConstantSheaf.fiberCounit_map_finiteLocallyConstantInternalPairing`: `ω` of the pairing
  of finite locally constant sheaves attached to `P` is `P`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

universe w v u u'

attribute [local instance] cartesianMonoidalSheafType braidedSheafType
  braidedContinuousGSetIsFinite braidedι_continuousGSetIsFinite
  cartesianMonoidalContinuousGSet braidedContinuousGSet

namespace CategoryTheory

section IsPairingBy

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C] (Φ : C ⥤ Type w)

/-- A morphism `h : X ⊗ Y ⟶ Z` out of a cartesian product **is given on `Φ`-elements by `f`**: the
image under `Φ` of an element is `f` of the images of its two projections. -/
def IsPairingBy {X Y Z : C} (h : X ⊗ Y ⟶ Z) (f : Φ.obj X → Φ.obj Y → Φ.obj Z) : Prop :=
  ∀ w, Φ.map h w = f (Φ.map (fst X Y) w) (Φ.map (snd X Y) w)

variable {Φ}

/-- Composing with `k` after a pairing given by `f`. -/
theorem IsPairingBy.comp {X Y Z Z' : C} {h : X ⊗ Y ⟶ Z} {f : Φ.obj X → Φ.obj Y → Φ.obj Z}
    (hf : IsPairingBy Φ h f) (k : Z ⟶ Z') :
    IsPairingBy Φ (h ≫ k) (fun a b => Φ.map k (f a b)) := fun w => by
  rw [Φ.map_comp, types_comp_apply, hf]

/-- A pairing given by `f` applied after a morphism `k` into the product. -/
private theorem IsPairingBy.map_comp_apply {W X Y Z : C} {h : X ⊗ Y ⟶ Z}
    {f : Φ.obj X → Φ.obj Y → Φ.obj Z} (hf : IsPairingBy Φ h f) (k : W ⟶ X ⊗ Y) (w : Φ.obj W) :
    Φ.map (k ≫ h) w = f (Φ.map (k ≫ fst X Y) w) (Φ.map (k ≫ snd X Y) w) := by
  simp only [Φ.map_comp, types_comp_apply]
  exact hf _

/-- Precomposing a pairing given by `f` with `a ⊗ b`. -/
theorem IsPairingBy.tensorHom_comp {X Y Z X' Y' : C} {h : X ⊗ Y ⟶ Z}
    {f : Φ.obj X → Φ.obj Y → Φ.obj Z} (hf : IsPairingBy Φ h f) (a : X' ⟶ X) (b : Y' ⟶ Y) :
    IsPairingBy Φ ((a ⊗ₘ b) ≫ h) (fun x y => f (Φ.map a x) (Φ.map b y)) := fun w => by
  rw [hf.map_comp_apply, tensorHom_fst, tensorHom_snd, Φ.map_comp, Φ.map_comp, types_comp_apply,
    types_comp_apply]

/-- A pairing given by `f` after a fully faithful monoidal functor `F` descends along `F`. -/
theorem IsPairingBy.preimage {D : Type*} [Category* D] [CartesianMonoidalCategory D]
    {F : C ⥤ D} [F.OplaxMonoidal] (hF : F.FullyFaithful) {Ψ : D ⥤ Type w} {X Y Z : C}
    {h : F.obj X ⊗ F.obj Y ⟶ F.obj Z} {f : Ψ.obj (F.obj X) → Ψ.obj (F.obj Y) → Ψ.obj (F.obj Z)}
    (hf : IsPairingBy Ψ h f) :
    IsPairingBy (F ⋙ Ψ) (hF.preimage (Functor.OplaxMonoidal.δ F X Y ≫ h)) f := fun w => by
  show Ψ.map (F.map _) w = f (Ψ.map (F.map (fst X Y)) w) (Ψ.map (F.map (snd X Y)) w)
  rw [hF.map_preimage, hf.map_comp_apply, Functor.OplaxMonoidal.δ_fst, Functor.OplaxMonoidal.δ_snd]

end IsPairingBy

end CategoryTheory

namespace Stacks.ConstantSheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G : Type u'} [Group G] [TopologicalSpace G]
  {e : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).FullSubcategory ≌
      (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).FullSubcategory}

attribute [local instance] braidedFiniteLocallyConstantSetSheaf
  braidedι_finiteLocallyConstantSetSheaf

/-- The underlying set of a finite continuous `G`-set. -/
abbrev finiteGSetForget (G : Type u') [Group G] [TopologicalSpace G] :
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).FullSubcategory ⥤ Type (max u v) :=
  ObjectProperty.ι _ ⋙ AlgebraicGeometry.ContinuousGSet.forget G

variable {ω : Sheaf J (Type (max u v)) ⥤ Type (max u v)}
  (σ : (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι ⋙ ω ≅
    e.functor ⋙ finiteGSetForget.{v, u} G)

/-- **The identification of `ω` on `e⁻¹A` with `A`**: the given identification `σ` of `ω` with the
underlying set of `e`, followed by the counit `e e⁻¹ A ≅ A`. -/
def fiberCounit (A : (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).FullSubcategory) :
    ω.obj ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.obj (e.inverse.obj A)) →
      (finiteGSetForget.{v, u} G).obj A :=
  fun z => (finiteGSetForget.{v, u} G).map (e.counitIso.hom.app A) (σ.hom.app (e.inverse.obj A) z)

/-- `fiberCounit` is a bijection. -/
theorem fiberCounit_bijective
    (A : (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).FullSubcategory) :
    Function.Bijective (fiberCounit σ A) :=
  ((σ.app (e.inverse.obj A)).toEquiv.trans
    ((finiteGSetForget.{v, u} G).mapIso (e.counitIso.app A)).toEquiv).bijective

/-- **`ω` of the morphism of finite locally constant sheaves attached by `e⁻¹` to a morphism
`ψ : A × B → T` of finite continuous `G`-sets is `ψ`**, under `fiberCounit`: if `ψ` is given on
elements by `f`, then `ω` of `e⁻¹A × e⁻¹B → e⁻¹(A × B) → e⁻¹T` is `f` on the two projections. -/
theorem fiberCounit_map_pairing
    {A B T : (AlgebraicGeometry.ContinuousGSet.isFinite.{u', max u v} G).FullSubcategory}
    (ψ : A ⊗ B ⟶ T)
    {Z : Type*} (g : (finiteGSetForget.{v, u} G).obj T → Z)
    (f : (finiteGSetForget.{v, u} G).obj A → (finiteGSetForget.{v, u} G).obj B → Z)
    (hψ : ∀ w, g ((finiteGSetForget.{v, u} G).map ψ w) =
      f ((finiteGSetForget.{v, u} G).map (fst A B) w) ((finiteGSetForget.{v, u} G).map (snd A B) w))
    (z : ω.obj ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.obj (e.inverse.obj A) ⊗
      (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.obj (e.inverse.obj B))) :
    letI : e.inverse.Braided := .ofChosenFiniteProducts _
    g (fiberCounit σ T (ω.map
        (Functor.LaxMonoidal.μ (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι _ _ ≫
        (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.map
          (Functor.LaxMonoidal.μ e.inverse A B ≫ e.inverse.map ψ)) z)) =
      f (fiberCounit σ A (ω.map (fst _ _) z)) (fiberCounit σ B (ω.map (snd _ _) z)) := by
  let : e.inverse.Braided := .ofChosenFiniteProducts _
  let ι := (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι
  let Φ := finiteGSetForget.{v, u} G
  let w := Φ.map (e.counitIso.hom.app (A ⊗ B))
    (Φ.map (e.functor.map (Functor.LaxMonoidal.μ e.inverse A B))
      (σ.hom.app _ (ω.map (Functor.LaxMonoidal.μ ι _ _) z)))
  have hσ : ∀ {X Y} (g : X ⟶ Y) (t : ω.obj (ι.obj X)),
      σ.hom.app Y (ω.map (ι.map g) t) = Φ.map (e.functor.map g) (σ.hom.app X t) := fun g t =>
    types_congr_hom (σ.hom.naturality g) t
  have hε : ∀ {X Y} (g : X ⟶ Y) (t : Φ.obj (e.functor.obj (e.inverse.obj X))),
      Φ.map (e.counitIso.hom.app Y) (Φ.map (e.functor.map (e.inverse.map g)) t) =
        Φ.map g (Φ.map (e.counitIso.hom.app X) t) := fun g t => by
    rw [← types_comp_apply (Φ.map _) (Φ.map _), ← types_comp_apply (Φ.map _) (Φ.map g),
      ← Φ.map_comp, ← Φ.map_comp]
    exact types_congr_hom (congrArg Φ.map (e.counitIso.hom.naturality g)) t
  have key : ∀ {Y} (p : A ⊗ B ⟶ Y), fiberCounit σ Y (ω.map (Functor.LaxMonoidal.μ ι _ _ ≫
      ι.map (Functor.LaxMonoidal.μ e.inverse A B ≫ e.inverse.map p)) z) = Φ.map p w := fun p => by
    simp only [fiberCounit, Functor.map_comp, types_comp_apply]
    rw [hσ, hσ, hε]
  rw [key, hψ, ← key, ← key, Functor.Monoidal.μ_fst, Functor.Monoidal.μ_fst,
    Functor.Monoidal.μ_snd, Functor.Monoidal.μ_snd]

section GSet

variable (G) in
/-- The underlying set of a continuous `G`-set, read off from the presheaf on the one-object
category of `G`. -/
theorem forget_map_eq_gsetPresheaf_map_app {X Y : AlgebraicGeometry.ContinuousGSet.{u', w} G}
    (h : X ⟶ Y) (t : (AlgebraicGeometry.ContinuousGSet.forget G).obj X) :
    (AlgebraicGeometry.ContinuousGSet.forget G).map h t =
      (gsetPresheaf.map h).app (SingleObj.star G) t :=
  rfl

attribute [local instance] braidedGsetPresheaf

/-- The internal pairing of continuous `G`-sets given by an equivariant biadditive map `P` is `P`
on elements. -/
theorem isPairingBy_gsetPresheafPairing (M N L : ContinuousGAddCommGrp.{u', w} G)
    (P : M.obj.obj.V →+ N.obj.obj.V →+ L.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.V) (b : N.obj.obj.V),
      P ((M.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.ρ g).asHom.hom b) = (L.obj.obj.ρ g).asHom.hom (P a b)) :
    IsPairingBy (AlgebraicGeometry.ContinuousGSet.forget G)
      (gsetPresheafFullyFaithful.preimage
        (Functor.OplaxMonoidal.δ gsetPresheaf (internalGModule M).X (internalGModule N).X ≫
          gsetPresheafPairing M N L P hP)) (fun a b => P a b) :=
  IsPairingBy.preimage (F := gsetPresheaf.{u', w} (G := G)) gsetPresheafFullyFaithful
    (Ψ := (evaluation _ _).obj (SingleObj.star G)) (h := gsetPresheafPairing M N L P hP)
    (f := fun a b => P a b) (fun _ => rfl)

/-- The isomorphism `commGrpContinuousGSetEquivalenceInverseIso` is the counit of
`CategoryTheory.commGrpContinuousGSetEquivalence` on underlying `G`-sets. -/
theorem commGrpContinuousGSetEquivalenceInverseIso_hom_hom (M : ContinuousGAddCommGrp.{u', w} G) :
    (commGrpContinuousGSetEquivalenceInverseIso M).hom.hom.hom.hom =
      (ContinuousGAddCommGrp.forgetAction G).map
        ((commGrpContinuousGSetEquivalence.{u', w} (G := G)).counitIso.hom.app M) := by
  have h := externalGModuleFullyFaithful.map_preimage
    (X := (commGrpContinuousGSetEquivalence.{u', w} (G := G)).inverse.obj M)
    (Y := internalGModule M)
    ((commGrpContinuousGSetEquivalence.{u', w} (G := G)).counitIso.hom.app M ≫
      (externalInternalGModuleIso M).inv)
  have h' := (congrArg (ContinuousGAddCommGrp.forgetAction G).map h).trans
    ((ContinuousGAddCommGrp.forgetAction G).map_comp _ _)
  refine h'.trans ?_
  refine (congrArg (_ ≫ ·) ?_).trans (Category.comp_id _)
  rfl

/-- `Stacks.ConstantSheaf.commGrpPairing` is `P` on elements, up to the identifications
`commGrpContinuousGSetEquivalenceInverseIso`. -/
theorem commGrpPairing_isPairingBy (M N L : ContinuousGAddCommGrp.{u', w} G)
    (P : M.obj.obj.V →+ N.obj.obj.V →+ L.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.V) (b : N.obj.obj.V),
      P ((M.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.ρ g).asHom.hom b) = (L.obj.obj.ρ g).asHom.hom (P a b)) :
    IsPairingBy (AlgebraicGeometry.ContinuousGSet.forget G) (commGrpPairing M N L P hP)
      (fun a b => (AlgebraicGeometry.ContinuousGSet.forget G).map
        (commGrpContinuousGSetEquivalenceInverseIso L).inv.hom.hom.hom
        (P ((AlgebraicGeometry.ContinuousGSet.forget G).map
            (commGrpContinuousGSetEquivalenceInverseIso M).hom.hom.hom.hom a)
          ((AlgebraicGeometry.ContinuousGSet.forget G).map
            (commGrpContinuousGSetEquivalenceInverseIso N).hom.hom.hom.hom b))) :=
  ((isPairingBy_gsetPresheafPairing M N L P hP).comp _).tensorHom_comp _ _

end GSet

section Finite

/-- The morphism of finite continuous `G`-sets underlying the counit of
`CategoryTheory.commGrpContinuousGSetEquivalence` at a finite discrete `G`-module: from the
`G`-set of the group object `finiteGModuleCommGrp G M` to the `G`-set underlying `M`. -/
def finiteGModuleCommGrpCounit (M : (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory) :
    (finiteGModuleCommGrp G M).X ⟶ (ContinuousGAddCommGrp.forgetActionIsFinite G).obj M :=
  ObjectProperty.homMk ((ContinuousGAddCommGrp.forgetAction G).map
    ((commGrpContinuousGSetEquivalence.{u', w} (G := G)).counitIso.hom.app M.obj))

/-- `finiteGModuleCommGrpCounit` is a bijection on underlying sets. -/
theorem finiteGModuleCommGrpCounit_bijective
    (M : (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory) :
    Function.Bijective ((finiteGSetForget.{w, w} G).map (finiteGModuleCommGrpCounit M)) :=
  ((AlgebraicGeometry.ContinuousGSet.forget G ⋙ 𝟭 _).mapIso
    ((ContinuousGAddCommGrp.forgetAction G).mapIso
      ((commGrpContinuousGSetEquivalence.{u', w} (G := G)).counitIso.app M.obj))).toEquiv.bijective

/-- **The pairing `finiteGModulePairing` of the group objects of finite `G`-modules is `P` on
elements**, under the counits `finiteGModuleCommGrpCounit`. -/
theorem finiteGModuleCommGrpCounit_finiteGModulePairing
    (M N L : (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.obj.ρ g).asHom.hom b) =
        (L.obj.obj.obj.ρ g).asHom.hom (P a b))
    (w : (finiteGSetForget.{w, w} G).obj
      ((finiteGModuleCommGrp G M).X ⊗ (finiteGModuleCommGrp G N).X)) :
    (finiteGSetForget.{w, w} G).map (finiteGModuleCommGrpCounit L)
        ((finiteGSetForget.{w, w} G).map (finiteGModulePairing M N L P hP) w) =
      P ((finiteGSetForget.{w, w} G).map (finiteGModuleCommGrpCounit M)
          ((finiteGSetForget.{w, w} G).map (fst _ _) w))
        ((finiteGSetForget.{w, w} G).map (finiteGModuleCommGrpCounit N)
          ((finiteGSetForget.{w, w} G).map (snd _ _) w)) := by
  have h := IsPairingBy.preimage
    (AlgebraicGeometry.ContinuousGSet.isFinite.{u', w} G).fullyFaithfulι
    (X := (finiteGModuleCommGrp G M).X) (Y := (finiteGModuleCommGrp G N).X)
    (Z := (finiteGModuleCommGrp G L).X)
    (((commGrpPairing_isPairingBy M.obj N.obj L.obj P hP).comp
      (ObjectProperty.commGrpιObjIso _
        (finiteGModuleCommGrpProp G L)).inv.hom.hom.hom.hom).tensorHom_comp
      (ObjectProperty.commGrpιObjIso _ (finiteGModuleCommGrpProp G M)).hom.hom.hom.hom.hom
      (ObjectProperty.commGrpιObjIso _ (finiteGModuleCommGrpProp G N)).hom.hom.hom.hom.hom) w
  refine (congrArg _ h).trans ?_
  have hκ : ∀ (A : (ContinuousGAddCommGrp.isFinite.{u', w} G).FullSubcategory) t,
      (finiteGSetForget.{w, w} G).map (finiteGModuleCommGrpCounit A) t =
        (AlgebraicGeometry.ContinuousGSet.forget G).map
          (commGrpContinuousGSetEquivalenceInverseIso A.obj).hom.hom.hom.hom t := fun A t =>
    (congrArg (fun k => (AlgebraicGeometry.ContinuousGSet.forget G).map k t)
      (commGrpContinuousGSetEquivalenceInverseIso_hom_hom A.obj)).symm
  rw [hκ, hκ]
  refine (hκ L _).trans ?_
  have H := types_congr_hom (congrArg (fun f => (AlgebraicGeometry.ContinuousGSet.forget G).map
    f.hom.hom.hom) (commGrpContinuousGSetEquivalenceInverseIso L.obj).inv_hom_id)
  exact (H _).trans rfl

end Finite

/-- **On fibres, the pairing of finite locally constant sheaves attached to `P` is `P`**: under
`fiberCounit` followed by `finiteGModuleCommGrpCounit`, `ω` of
`Stacks.ConstantSheaf.finiteLocallyConstantInternalPairing` is `P` on the two projections. -/
theorem fiberCounit_map_finiteLocallyConstantInternalPairing
    (M N L : (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory)
    (P : M.obj.obj.obj.V →+ N.obj.obj.obj.V →+ L.obj.obj.obj.V)
    (hP : ∀ (g : G) (a : M.obj.obj.obj.V) (b : N.obj.obj.obj.V),
      P ((M.obj.obj.obj.ρ g).asHom.hom a) ((N.obj.obj.obj.ρ g).asHom.hom b) =
        (L.obj.obj.obj.ρ g).asHom.hom (P a b))
    (z : ω.obj ((isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.obj
        (e.inverse.obj (finiteGModuleCommGrp G M).X) ⊗
      (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.obj
        (e.inverse.obj (finiteGModuleCommGrp G N).X))) :
    (finiteGSetForget.{v, u} G).map (finiteGModuleCommGrpCounit L)
        (fiberCounit σ _ (ω.map (finiteLocallyConstantInternalPairing J e M N L P hP) z)) =
      P ((finiteGSetForget.{v, u} G).map (finiteGModuleCommGrpCounit M)
          (fiberCounit σ _ (ω.map (fst _ _) z)))
        ((finiteGSetForget.{v, u} G).map (finiteGModuleCommGrpCounit N)
          (fiberCounit σ _ (ω.map (snd _ _) z))) :=
  fiberCounit_map_pairing σ (finiteGModulePairing M N L P hP) _
    (fun a b => P ((finiteGSetForget.{v, u} G).map (finiteGModuleCommGrpCounit M) a)
      ((finiteGSetForget.{v, u} G).map (finiteGModuleCommGrpCounit N) b))
    (finiteGModuleCommGrpCounit_finiteGModulePairing M N L P hP) z

variable (J e) in
/-- The sheaf of sets underlying the finite locally constant abelian sheaf attached to `A` by
Tag 0DV5 (2) is `e⁻¹` of the `G`-set of the group object of `A`. -/
theorem sheafCompose_forget_finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v}]
    (A : (ContinuousGAddCommGrp.isFinite.{u', max u v} G).FullSubcategory) :
    (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max u v})).obj
        ((finiteLocallyConstantAbelianEquivalenceOfSetEquivalence J G e).inverse.obj A).obj =
      (isFiniteLocallyConstantSetSheaf.{v, u, u} J).ι.obj
        (e.inverse.obj (finiteGModuleCommGrp G A).X) :=
  (congrArg (sheafCompose J (CategoryTheory.forget AddCommGrpCat.{max u v})).obj
    (finiteLocallyConstantAbelianEquivalenceOfSetEquivalence_inverse_obj_obj J G e A)).trans rfl

open scoped Obj in
/-- The pairing of sections `Sites.AbelianSheaf.sectionsPairing` of a bimultiplicative `β` is `β`
on a section of the product sheaf whose two projections are the given sections. -/
theorem exists_sectionsPairing_eq_app {R S T : CommGrp (Sheaf J (Type (max u v)))}
    {β : R.X ⊗ S.X ⟶ T.X} (hβ : IsBimultiplicative β) (U : Cᵒᵖ)
    (a : ((Sites.AbelianSheaf.externalSheaf J).obj R).obj.obj U)
    (b : ((Sites.AbelianSheaf.externalSheaf J).obj S).obj.obj U) :
    ∃ w : (R.X ⊗ S.X).obj.obj U, (fst R.X S.X).hom.app U w = Additive.toMul a ∧
      (snd R.X S.X).hom.app U w = Additive.toMul b ∧
      Additive.toMul (Sites.AbelianSheaf.sectionsPairing hβ U a b) = β.hom.app U w := by
  let : (sheafToPresheaf J (Type (max u v))).Braided := .ofChosenFiniteProducts _
  refine ⟨(Functor.LaxMonoidal.μ (sheafToPresheaf J (Type (max u v))) R.X S.X).app U
    (Additive.toMul a, Additive.toMul b), ?_, ?_, rfl⟩
  · exact types_congr_hom (congr_app (Functor.Monoidal.μ_fst (sheafToPresheaf J (Type (max u v)))
      R.X S.X) U) _
  · exact types_congr_hom (congr_app (Functor.Monoidal.μ_snd (sheafToPresheaf J (Type (max u v)))
      R.X S.X) U) _

end Stacks.ConstantSheaf

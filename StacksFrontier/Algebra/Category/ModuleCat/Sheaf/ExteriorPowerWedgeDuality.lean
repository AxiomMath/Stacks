module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorAlgebraPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreePowerSheafify
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PowerPresentationSequences
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceExteriorAlgebraSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.CartesianAffinePresentation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomComplex
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree
public import StacksFrontier.LinearAlgebra.ExteriorPower.WedgeBasisDuality

/-!
# Exterior powers of a locally free sheaf of modules are dual to each other

Let `F` be a sheaf of modules on a site which is locally free of rank `n`, and let `a + b = n`.
The wedge product `⋀ᵃ F ⊗ ⋀ᵇ F ⟶ ⋀ⁿ F` identifies `⋀ᵃ F` with the sheaf-hom
`SheafHom(⋀ᵇ F, ⋀ⁿ F)`: a local section `x` of `⋀ᵃ F` is sent to `y ↦ x ∧ y`. For the sheaf of
differentials `Ω_{X/k}` of a smooth scheme of dimension `d` this is the isomorphism
`Ω^{d - p}_{X/k} ≅ SheafHom(Ω^p_{X/k}, Ω^d_{X/k})` used in the proof of [Stacks, Tag 0FW4].

## Main definitions

* `PresheafOfModules.descOfBasis`: on a category with a terminal object `T`, a presheaf of modules
  whose sections carry bases restricted from those over `T` is free: a morphism out of it is the
  same as a family of sections over `T`.
* `SheafOfModules.GradedAlgebra.mulSection`: multiplication by a global section of a sheaf of
  graded algebras, `y ↦ x ∧ y`, as a morphism of sheaves of modules.

## Main results

* `PresheafOfModules.bijective_evalBasis`: the freeness statement above.
* `SheafOfModules.GradedAlgebra.bijective_mulSection_iff_of_iso`: bijectivity of
  `x ↦ mulSection x` is invariant under multiplicative isomorphisms of graded algebras.

## References

* [Stacks Project, Tag 0FW4](https://stacks.math.columbia.edu/tag/0FW4)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u₁ u

namespace CategoryTheory.Over

/-- The morphism from `Y` to the terminal object `Over.mk (𝟙 X)` of `Over X` is
`Over.homMk Y.hom`, so that restricting along it is restricting along `Y.hom`. -/
@[simp]
theorem isTerminalMkId_from {C : Type*} [Category C] (X : C) (Y : Over X) :
    (isTerminalMkId X).from Y = Over.homMk Y.hom (Category.comp_id _) :=
  rfl

end CategoryTheory.Over

namespace PresheafOfModules

/-! ### Presheaves of modules with bases restricted from a terminal object -/

/-- Restricting a section over the terminal object `T` to `T` itself does nothing. -/
private theorem map_from_terminal_self {D : Type*} [Category D] {R : Dᵒᵖ ⥤ RingCat.{u}} {T : D}
    (hT : IsTerminal T) (P : PresheafOfModules.{v} R) (z : P.obj (op T)) :
    P.map (hT.from T).op z = z := by
  have h : (hT.from T).op = 𝟙 (op T) := Quiver.Hom.unop_inj (hT.hom_ext _ _)
  rw [P.congr_map_apply h, map_id]
  rfl

section FreeOnTerminal

variable {D : Type*} [Category D] {R : Dᵒᵖ ⥤ RingCat.{u}} {T : D} (hT : IsTerminal T)
  {P Q : PresheafOfModules.{v} R} {S : Type*} (b : ∀ V : Dᵒᵖ, Module.Basis S (R.obj V) (P.obj V))
  (hb : ∀ (V : Dᵒᵖ) (s : S), P.map (hT.from V.unop).op (b (op T) s) = b V s)

include hb in
/-- The bases are carried into each other by the restriction maps. -/
theorem map_basis_of_isTerminal {V W : Dᵒᵖ} (f : V ⟶ W) (s : S) : P.map f (b V s) = b W s := by
  rw [← hb V s, ← P.map_comp_apply, ← hb W s]
  exact P.congr_map_apply (Quiver.Hom.unop_inj (hT.hom_ext _ _)) _

/-- **A presheaf of modules with bases restricted from a terminal object is free.** A family of
sections of `Q` over the terminal object `T`, indexed by the basis, extends to the morphism
`P ⟶ Q` sending the basis vector `b V s` to the restriction of the given section to `V`. -/
noncomputable def descOfBasis (q : S → Q.obj (op T)) : P ⟶ Q where
  app V := ModuleCat.ofHom ((b V).constr ℕ fun s => Q.map (hT.from V.unop).op (q s))
  naturality {V W} f := by
    refine ModuleCat.hom_ext ((b V).ext fun s => ?_)
    change (b W).constr ℕ (fun s => Q.map (hT.from W.unop).op (q s)) (P.map f (b V s)) =
      Q.map f ((b V).constr ℕ (fun s => Q.map (hT.from V.unop).op (q s)) (b V s))
    rw [map_basis_of_isTerminal hT b hb f s, Module.Basis.constr_basis,
      Module.Basis.constr_basis, ← Q.map_comp_apply]
    exact Q.congr_map_apply (Quiver.Hom.unop_inj (hT.hom_ext _ _)) _

/-- The morphism `descOfBasis hT b hb q` sends the basis vector `b V s` to the restriction of
`q s` to `V`. -/
theorem descOfBasis_app_basis (q : S → Q.obj (op T)) (V : Dᵒᵖ) (s : S) :
    (descOfBasis hT b hb q).app V (b V s) = Q.map (hT.from V.unop).op (q s) :=
  (b V).constr_basis ℕ _ s

include hb in
/-- **Morphisms out of a presheaf of modules with bases restricted from a terminal object are
families of sections over the terminal object**: a morphism `φ : P ⟶ Q` is determined by the
values `φ_T(b_T s)`, and every family of values occurs. -/
theorem bijective_evalBasis :
    Function.Bijective (fun φ : P ⟶ Q => fun s => φ.app (op T) (b (op T) s)) := by
  refine ⟨fun φ ψ h => ?_, fun q => ⟨descOfBasis hT b hb q, funext fun s => ?_⟩⟩
  · refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext ((b V).ext fun s => ?_)
    change φ.app V (b V s) = ψ.app V (b V s)
    rw [← hb V s, naturality_apply, naturality_apply]
    exact congrArg _ (congrFun h s)
  · change (descOfBasis hT b hb q).app (op T) (b (op T) s) = q s
    rw [descOfBasis_app_basis, map_from_terminal_self]

end FreeOnTerminal

end PresheafOfModules

namespace SheafOfModules.GradedAlgebra

/-! ### Multiplication by a global section -/

variable {D : Type*} [Category D] {K : GrothendieckTopology D} {R : Sheaf K RingCat}
  {T : D} (hT : IsTerminal T)

/-- **Multiplication by a section over the terminal object.** For a sheaf of graded algebras `E`
and a section `x` of `E_i` over the terminal object `T`, the morphism of sheaves of modules
`E_j ⟶ E_{i + j}` given on sections over `V` by `y ↦ x|_V · y`. -/
noncomputable def mulSection (E : GradedAlgebra R) (i j : ℤ) (x : (E.piece i).val.obj (op T)) :
    E.piece j ⟶ E.piece (i + j) where
  val :=
    { app V := ModuleCat.ofHom
        { toFun y := (E.mul i j).app V ((E.piece i).val.map (hT.from V.unop).op x) y
          map_add' y y' := map_add _ y y'
          map_smul' r y := (E.mul i j).map_smul_right V r _ y }
      naturality {V W} f := by
        refine ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
        change (E.mul i j).app W ((E.piece i).val.map (hT.from W.unop).op x)
            ((E.piece j).val.map f y) =
          (E.piece (i + j)).val.map f
            ((E.mul i j).app V ((E.piece i).val.map (hT.from V.unop).op x) y)
        refine Eq.trans ?_ ((E.mul i j).naturality f _ y).symm
        refine congrArg (fun z => (E.mul i j).app W z ((E.piece j).val.map f y)) ?_
        rw [← (E.piece i).val.map_comp_apply]
        exact (E.piece i).val.congr_map_apply (Quiver.Hom.unop_inj (hT.hom_ext _ _)) x }

/-- On sections over `V`, `mulSection hT E i j x` is `y ↦ x|_V · y`. -/
theorem mulSection_app (E : GradedAlgebra R) (i j : ℤ) (x : (E.piece i).val.obj (op T))
    (V : Dᵒᵖ) (y : (E.piece j).val.obj V) :
    (mulSection hT E i j x).val.app V y =
      (E.mul i j).app V ((E.piece i).val.map (hT.from V.unop).op x) y :=
  rfl

/-- **Transport along a multiplicative isomorphism.** If degreewise isomorphisms `e_i`, `e_j`,
`e_{i+j}` between two sheaves of graded algebras are compatible with the multiplications, then
multiplication by the image of `x` is multiplication by `x` conjugated by the isomorphisms. -/
theorem mulSection_iso {E E' : GradedAlgebra R} {i j : ℤ} (ei : E.piece i ≅ E'.piece i)
    (ej : E.piece j ≅ E'.piece j) (eij : E.piece (i + j) ≅ E'.piece (i + j))
    (he : ∀ (V : Dᵒᵖ) (x : (E.piece i).val.obj V) (y : (E.piece j).val.obj V),
      eij.hom.val.app V ((E.mul i j).app V x y) =
        (E'.mul i j).app V (ei.hom.val.app V x) (ej.hom.val.app V y))
    (x : (E.piece i).val.obj (op T)) :
    mulSection hT E' i j (ei.hom.val.app (op T) x) = ej.inv ≫ mulSection hT E i j x ≫ eij.hom := by
  ext V y
  change (E'.mul i j).app V ((E'.piece i).val.map (hT.from V.unop).op
      (ei.hom.val.app (op T) x)) y =
    eij.hom.val.app V ((E.mul i j).app V ((E.piece i).val.map (hT.from V.unop).op x)
      (ej.inv.val.app V y))
  convert (he V ((E.piece i).val.map (hT.from V.unop).op x) (ej.inv.val.app V y)).symm using 2
  · exact congrArg _ (PresheafOfModules.naturality_apply ei.hom.val (hT.from V.unop).op x).symm
  · exact (congrArg (fun g => g.val.app V y) ej.inv_hom_id).symm

/-- **Bijectivity of multiplication by global sections is invariant under multiplicative
isomorphisms.** -/
theorem bijective_mulSection_iff_of_iso {E E' : GradedAlgebra R} {i j : ℤ}
    (ei : E.piece i ≅ E'.piece i) (ej : E.piece j ≅ E'.piece j)
    (eij : E.piece (i + j) ≅ E'.piece (i + j))
    (he : ∀ (V : Dᵒᵖ) (x : (E.piece i).val.obj V) (y : (E.piece j).val.obj V),
      eij.hom.val.app V ((E.mul i j).app V x y) =
        (E'.mul i j).app V (ei.hom.val.app V x) (ej.hom.val.app V y)) :
    Function.Bijective (mulSection hT E i j) ↔ Function.Bijective (mulSection hT E' i j) := by
  let c : (E.piece j ⟶ E.piece (i + j)) ≃ (E'.piece j ⟶ E'.piece (i + j)) :=
    { toFun g := ej.inv ≫ g ≫ eij.hom
      invFun g := ej.hom ≫ g ≫ eij.inv
      left_inv g := by simp
      right_inv g := by simp }
  let eX : (E.piece i).val.obj (op T) ≃ (E'.piece i).val.obj (op T) :=
    { toFun x := ei.hom.val.app (op T) x
      invFun x := ei.inv.val.app (op T) x
      left_inv x := congrArg (fun g => g.val.app (op T) x) ei.hom_inv_id
      right_inv x := congrArg (fun g => g.val.app (op T) x) ei.inv_hom_id }
  have h : mulSection hT E' i j ∘ eX = c ∘ mulSection hT E i j :=
    funext fun x => mulSection_iso hT ei ej eij he x
  rw [← Function.Bijective.of_comp_iff _ eX.bijective, h,
    Function.Bijective.of_comp_iff' c.bijective]

end SheafOfModules.GradedAlgebra

namespace PresheafOfModules

/-! ### The sheafification unit at a presheaf isomorphic to a sheaf -/

section SheafifyUnit

variable {C : Type*} [Category C] {J : GrothendieckTopology C} {R₀ : Cᵒᵖ ⥤ RingCat}
  {R : Sheaf J RingCat} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat]

/-- **The sheafification unit is invertible at a presheaf of modules isomorphic to a sheaf.** The
counit of the sheafification adjunction is invertible, so by the triangle identity the unit is
invertible at the underlying presheaf of a sheaf, and the unit is natural. -/
theorem isIso_sheafifyUnit_of_iso {M : PresheafOfModules R₀} {G : SheafOfModules R}
    (e : M ≅ (SheafOfModules.forget R ⋙ restrictScalars α).obj G) :
    IsIso (sheafifyUnit α M) := by
  let adj := sheafificationAdjunction α
  let Rf := SheafOfModules.forget R ⋙ restrictScalars α
  have h1 : IsIso (adj.unit.app (Rf.obj G)) := by
    have h : IsIso (adj.unit.app (Rf.obj G) ≫ Rf.map (adj.counit.app G)) := by
      rw [adj.right_triangle_components G]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (Rf.map (adj.counit.app G))
  have h3 := adj.unit.naturality e.inv
  rw [Functor.id_map] at h3
  have h4 : adj.unit.app M =
      e.hom ≫ adj.unit.app (Rf.obj G) ≫ (sheafification α ⋙ Rf).map e.inv := by
    rw [← h3, Iso.hom_inv_id_assoc]
  change IsIso (adj.unit.app M)
  rw [h4]
  infer_instance

end SheafifyUnit

end PresheafOfModules

namespace Stacks.SheafOfModules.WedgeDuality

/-! ### The free case -/

open CategoryTheory.Sheaf _root_.SheafOfModules.GradedAlgebra

variable {D : Type u₁} [Category.{v} D] (K : GrothendieckTopology D)
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {Osharp : Sheaf K CommRingCat.{u}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  {T : D} (hT : IsTerminal T) (ι : Type u) [LinearOrder ι] [Fintype ι]

omit [Fintype ι] in
/-- The sectionwise exterior powers of a finite free sheaf of modules are already sheaves, so the
sheafification unit is invertible at them. -/
theorem isIso_sheafifyUnit_extPow_free [Finite ι] (k : ℕ) :
    IsIso (PresheafOfModules.sheafifyUnit (toRingCatMap K (𝟙 Osharp.obj))
      (PresheafOfModules.extPow k (_root_.SheafOfModules.valPresheaf K
        (_root_.SheafOfModules.free (R := toRingCat K Osharp) ι)))) :=
  PresheafOfModules.isIso_sheafifyUnit_of_iso _
    (G := _root_.SheafOfModules.free (R := toRingCat K Osharp) (Set.powersetCard ι k))
    (extPowFreeIso (toRingCat K Osharp).property k)

/-- **The wedge pairing is perfect for a finite free sheaf of modules, over a terminal object.**
On a site with a terminal object `T`, for the exterior algebra of `free ι` with `a + b = #ι`,
every morphism `⋀ᵇ ⟶ ⋀ᵃ⁺ᵇ` is multiplication by exactly one section of `⋀ᵃ` over `T`.

The exterior algebra is the chosen one, the degreewise sheafification of the sectionwise exterior
algebra. Its pieces are sheafifications of presheaves which are already sheaves, so the
sheafification units identify the sections with the sectionwise exterior powers and the
multiplication with the wedge product; the sheafification adjunction and the natural basis of the
sectionwise exterior power reduce a morphism `⋀ᵇ ⟶ ⋀ᵃ⁺ᵇ` to its values on the basis over `T`,
and `exteriorPower.wedgeBasisMap_bijective` concludes. -/
theorem bijective_mulSection_algebras_free {a b : ℕ} (hab : a + b = Fintype.card ι) :
    Function.Bijective (mulSection hT
      (_root_.SheafOfModules.algebras K
        (_root_.SheafOfModules.free (R := toRingCat K Osharp) ι)).exterior
      (a : ℤ) (b : ℤ)) := by
  classical
  let E := (_root_.SheafOfModules.algebras K
    (_root_.SheafOfModules.free (R := toRingCat K Osharp) ι)).exterior
  let α := toRingCatMap K (𝟙 Osharp.obj)
  let P : ℕ → PresheafOfModules _ := fun k => PresheafOfModules.extPow k
    (_root_.SheafOfModules.valPresheaf K (_root_.SheafOfModules.free (R := toRingCat K Osharp) ι))
  let adj := PresheafOfModules.sheafificationAdjunction α
  let hO := (toRingCat K Osharp).property
  have hu : ∀ (k : ℕ) (V : Dᵒᵖ),
      Function.Bijective ((PresheafOfModules.sheafifyUnit α (P k)).app V) := fun k V => by
    have := isIso_sheafifyUnit_extPow_free K (Osharp := Osharp) ι k
    have : IsIso ((PresheafOfModules.sheafifyUnit α (P k)).app V) :=
      Functor.map_isIso (PresheafOfModules.evaluation _ V) (PresheafOfModules.sheafifyUnit α (P k))
    exact ConcreteCategory.bijective_of_isIso ((PresheafOfModules.sheafifyUnit α (P k)).app V)
  let e : ∀ V : Dᵒᵖ, Module.Basis _ _ ((P b).obj V) := fun V => basisExtPowSections hO b V
  have he : ∀ (V : Dᵒᵖ) (s : Set.powersetCard ι b),
      (P b).map (hT.from V.unop).op (e (op T) s) = e V s := fun V s =>
    basisExtPowSections_map hO b _ s
  let Ψ := fun φ : P b ⟶ (_root_.SheafOfModules.forget _ ⋙
      PresheafOfModules.restrictScalars α).obj (E.piece ((a : ℤ) + (b : ℤ))) =>
    fun s => φ.app (op T) (e (op T) s)
  have hΨ : Function.Bijective Ψ := PresheafOfModules.bijective_evalBasis hT e he
  have hA := (adj.homEquiv (P b) (E.piece ((a : ℤ) + (b : ℤ)))).bijective
  let W := exteriorPower.wedgeBasisMap (freeCoordBasis hO (ι := ι) (op T)) a b
  have hW : Function.Bijective W := exteriorPower.wedgeBasisMap_bijective _ hab
  have key : ∀ x₀ : (P a).obj (op T),
      Ψ (adj.homEquiv _ _ (mulSection hT E a b
        ((PresheafOfModules.sheafifyUnit α (P a)).app (op T) x₀))) =
      fun s => (PresheafOfModules.sheafifyUnit α (P (a + b))).app (op T) (W x₀ s) := by
    intro x₀
    funext s
    have h2 := Stacks.GradedAlgebra.sheafify_mul_unit α
      (PresheafOfModules.extPowGradedAlgebra (_root_.SheafOfModules.valPresheaf K
        (_root_.SheafOfModules.free (R := toRingCat K Osharp) ι))).extend (a : ℤ) (b : ℤ)
      (op T) x₀ (e (op T) s)
    simp only [Ψ]
    change (E.mul (a : ℤ) (b : ℤ)).app (op T) ((E.piece (a : ℤ)).val.map (hT.from T).op
        ((PresheafOfModules.sheafifyUnit α (P a)).app (op T) x₀))
        ((PresheafOfModules.sheafifyUnit α (P b)).app (op T) (e (op T) s)) = _
    refine (congrArg (fun z => (E.mul (a : ℤ) (b : ℤ)).app (op T) z
      ((PresheafOfModules.sheafifyUnit α (P b)).app (op T) (e (op T) s)))
      (PresheafOfModules.map_from_terminal_self hT (E.piece (a : ℤ)).val _)).trans ?_
    exact h2.trans (congrArg _ (Subtype.ext rfl))
  have h1 : Function.Bijective ((fun z => fun s =>
      (PresheafOfModules.sheafifyUnit α (P (a + b))).app (op T) (z s)) ∘ W) :=
    (show Function.Bijective (fun z : Set.powersetCard ι b → (P (a + b)).obj (op T) => fun s =>
      (PresheafOfModules.sheafifyUnit α (P (a + b))).app (op T) (z s)) from
      ⟨(hu (a + b) (op T)).1.comp_left, (hu (a + b) (op T)).2.comp_left⟩).comp hW
  have h2 : (Ψ ∘ adj.homEquiv _ _) ∘ mulSection hT E a b ∘
      (PresheafOfModules.sheafifyUnit α (P a)).app (op T) =
      (fun z => fun s => (PresheafOfModules.sheafifyUnit α (P (a + b))).app (op T) (z s)) ∘ W :=
    funext key
  rw [← h2] at h1
  exact (Function.Bijective.of_comp_iff _ (hu a (op T))).1
    ((Function.Bijective.of_comp_iff' (hΨ.comp hA) _).1 h1)

/-- **The wedge pairing is perfect for every exterior algebra of a sheaf of modules isomorphic to
a finite free one, over a terminal object.** The exterior algebra `E` is compared with the chosen
exterior algebra of `free ι` by the canonical isomorphism of exterior algebras, which is
multiplicative, and `bijective_mulSection_algebras_free` applies to the latter. -/
theorem bijective_mulSection_of_iso_free
    {M : _root_.SheafOfModules.{u} (toRingCat K Osharp)}
    {E : _root_.SheafOfModules.GradedAlgebra.{u, u} (toRingCat K Osharp)} {gen : M ⟶ E.piece 1}
    (hE : IsExteriorAlgebra E gen)
    (e : M ≅ _root_.SheafOfModules.free (R := toRingCat K Osharp) ι) {a b : ℕ}
    (hab : a + b = Fintype.card ι) :
    Function.Bijective (mulSection hT E (a : ℤ) (b : ℤ)) := by
  let B := _root_.SheafOfModules.algebras K (_root_.SheafOfModules.free (R := toRingCat K Osharp) ι)
  have hE' : IsExteriorAlgebra E (e.inv ≫ gen) := hE.comp_iso e.inv inferInstance
  have hB := B.exterior_isExteriorAlgebra
  rw [bijective_mulSection_iff_of_iso hT (hE'.pieceIso hB (a : ℤ)) (hE'.pieceIso hB (b : ℤ))
    (hE'.pieceIso hB ((a : ℤ) + (b : ℤ)))
    (fun V x y => IsUniversal.pieceIso_mul hE' hB (a : ℤ) (b : ℤ) V x y)]
  exact bijective_mulSection_algebras_free K hT ι hab

end Stacks.SheafOfModules.WedgeDuality

namespace Stacks.SheafOfModules.WedgeDuality

/-! ### Over an object trivialising the sheaf of modules -/

open CategoryTheory.Sheaf _root_.SheafOfModules.GradedAlgebra

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

/-- **The wedge pairing is perfect over an object trivialising the module.** Let `E` be an
exterior algebra of a sheaf of modules `F` and let `U` be an object over which `F` is free on a
finite linearly ordered type `ι`, with `a + b = #ι`. Then every morphism `⋀ᵇ F|_U ⟶ ⋀ᵃ⁺ᵇ F|_U` on
the slice site over `U` is multiplication by exactly one section of `⋀ᵃ F` over `U`.

The restriction of `E` to the slice site is an exterior algebra of `F|_U`
(`Stacks.SheafOfModules.SliceExterior.isExteriorAlgebra_over`) with the same multiplication, and
`Over.mk (𝟙 U)` is terminal in the slice category. -/
theorem bijective_mulSection_over (U : C)
    [(J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [(J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    {F : _root_.SheafOfModules.{u} (toRingCat J Osharp)}
    {E : _root_.SheafOfModules.GradedAlgebra.{u, u} (toRingCat J Osharp)} {gen : F ⟶ E.piece 1}
    (hE : IsExteriorAlgebra E gen) (ι : Type u) [LinearOrder ι] [Fintype ι]
    (e : F.over U ≅ _root_.SheafOfModules.free (R := (toRingCat J Osharp).over U) ι) {a b : ℕ}
    (hab : a + b = Fintype.card ι) :
    Function.Bijective (mulSection (Over.isTerminalMkId U) (E.over U) (a : ℤ) (b : ℤ)) :=
  bijective_mulSection_of_iso_free (J.over U) (Osharp := Osharp.over U) (Over.isTerminalMkId U) ι
    (Stacks.SheafOfModules.SliceExterior.isExteriorAlgebra_over U F E gen hE) e hab

end Stacks.SheafOfModules.WedgeDuality

namespace Stacks.SheafOfModules.WedgeDuality

/-! ### The wedge pairing as a morphism into the sheaf-hom -/

section Global

open CategoryTheory.Sheaf _root_.SheafOfModules.GradedAlgebra _root_.AlgebraicGeometry

-- The sections of `AlgebraicGeometry.RingedSite.internalHomSheaf` are modules over
-- `Stacks.SheafOfModules.Tensor.ringSheaf O`, a `def` whose underlying presheaf is
-- `O.obj ⋙ forget₂ _ _`, the presheaf of `CategoryTheory.Sheaf.toRingCat J O`; unification has to
-- see through it to identify the two rings of sections.
attribute [local implicit_reducible] Stacks.SheafOfModules.Tensor.ringSheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]

variable (J Osharp) in
/-- The site `(C, J)` with the sheaf of commutative rings `O♯`, as a ringed site. -/
abbrev toRingedSite : RingedSite.{u, u, u} := ⟨C, J, Osharp⟩

variable (E : _root_.SheafOfModules.GradedAlgebra.{u, u} (toRingCat J Osharp)) (i j : ℤ)

/-- The section of `SheafHom(E_j, E_{i+j})` over `U` given by multiplication by a section `x` of
`E_i` over `U`: on the slice site over `U` it is `y ↦ x|_V · y`. -/
noncomputable def wedgeHomApp (U : C) (x : (E.piece i).val.obj (op U)) :
    (RingedSite.internalHomSheaf (toRingedSite J Osharp) (E.piece j)
      (E.piece (i + j))).val.obj (op U) :=
  (mulSection (Over.isTerminalMkId U) (E.over U) i j x).val

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- On sections over an object `V` of the slice over `U`, `wedgeHomApp E i j U x` is
`y ↦ x|_V · y`. -/
theorem wedgeHomApp_app (U : C) (x : (E.piece i).val.obj (op U)) (V : (Over U)ᵒᵖ)
    (y : (E.piece j).val.obj (op V.unop.left)) :
    (wedgeHomApp E i j U x).app V y =
      (E.mul i j).app (op V.unop.left) ((E.piece i).val.map V.unop.hom.op x) y :=
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- `wedgeHomApp E i j U` is additive in the section `x`. -/
theorem wedgeHomApp_add (U : C) (x x' : (E.piece i).val.obj (op U)) :
    wedgeHomApp E i j U (x + x') = wedgeHomApp E i j U x + wedgeHomApp E i j U x' := by
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  change (E.mul i j).app (op V.unop.left) ((E.piece i).val.map V.unop.hom.op (x + x')) y =
    (E.mul i j).app (op V.unop.left) ((E.piece i).val.map V.unop.hom.op x) y +
      (E.mul i j).app (op V.unop.left) ((E.piece i).val.map V.unop.hom.op x') y
  have h : (E.piece i).val.map V.unop.hom.op (x + x') =
      (E.piece i).val.map V.unop.hom.op x + (E.piece i).val.map V.unop.hom.op x' :=
    map_add _ x x'
  exact (congrArg (fun z => (E.mul i j).app (op V.unop.left) z y) h).trans
    (DFunLike.congr_fun (map_add ((E.mul i j).app (op V.unop.left)) _ _) y)

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- `wedgeHomApp E i j U` is linear over the sections of the structure sheaf over `U`. -/
theorem wedgeHomApp_smul (U : C) (r : (toRingCat J Osharp).obj.obj (op U))
    (x : (E.piece i).val.obj (op U)) :
    letI := homModule (toRingedSite J Osharp).O.obj
      ((toRingedSite J Osharp).valOf (E.piece j))
      ((toRingedSite J Osharp).valOf (E.piece (i + j))) U
    wedgeHomApp E i j U (r • x) = r • wedgeHomApp E i j U x := by
  let := homModule (toRingedSite J Osharp).O.obj
    ((toRingedSite J Osharp).valOf (E.piece j)) ((toRingedSite J Osharp).valOf (E.piece (i + j))) U
  refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
  change (E.mul i j).app (op V.unop.left) ((E.piece i).val.map V.unop.hom.op (r • x)) y =
    ((toRingCat J Osharp).obj.map V.unop.hom.op).hom r •
      (E.mul i j).app (op V.unop.left) ((E.piece i).val.map V.unop.hom.op x) y
  have h : (E.piece i).val.map V.unop.hom.op (r • x) =
      ((toRingCat J Osharp).obj.map V.unop.hom.op).hom r • (E.piece i).val.map V.unop.hom.op x :=
    (E.piece i).val.map_smul _ r x
  exact (congrArg (fun z => (E.mul i j).app (op V.unop.left) z y) h).trans
    ((E.mul i j).map_smul_left _ _ _ y)

/-- **The wedge pairing `⋀ⁱ ⟶ SheafHom(⋀ʲ, ⋀ⁱ⁺ʲ)`** of a sheaf of graded algebras: a local section
`x` of `E_i` over `U` goes to the morphism `E_j|_U ⟶ E_{i+j}|_U`, `y ↦ x · y`. The sheaf-hom is
`AlgebraicGeometry.RingedSite.internalHomSheaf`, the one the derived internal hom is built from. -/
noncomputable def wedgeHom :
    E.piece i ⟶
      RingedSite.internalHomSheaf (toRingedSite J Osharp) (E.piece j) (E.piece (i + j)) where
  val :=
    { app U :=
        letI := homModule (toRingedSite J Osharp).O.obj ((toRingedSite J Osharp).valOf (E.piece j))
          ((toRingedSite J Osharp).valOf (E.piece (i + j))) U.unop
        ModuleCat.ofHom
        { toFun := wedgeHomApp E i j U.unop
          map_add' := wedgeHomApp_add E i j U.unop
          map_smul' := wedgeHomApp_smul E i j U.unop }
      naturality {U W} f := by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        refine PresheafOfModules.hom_ext fun V => ModuleCat.hom_ext (LinearMap.ext fun y => ?_)
        change (E.mul i j).app (op V.unop.left)
            ((E.piece i).val.map V.unop.hom.op ((E.piece i).val.map f x)) y =
          (E.mul i j).app (op V.unop.left) ((E.piece i).val.map (V.unop.hom ≫ f.unop).op x) y
        exact congrArg (fun z => (E.mul i j).app (op V.unop.left) z y)
          ((E.piece i).val.map_comp_apply f V.unop.hom.op x).symm }

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- On sections over `U`, the wedge pairing sends `x` to multiplication by `x` on the slice site
over `U`. -/
theorem wedgeHom_val_app (U : C) (x : (E.piece i).val.obj (op U)) :
    (wedgeHom E i j).val.app (op U) x =
      (mulSection (Over.isTerminalMkId U) (E.over U) i j x).val :=
  rfl

omit [J.WEqualsLocallyBijective AddCommGrpCat] [HasWeakSheafify J AddCommGrpCat] in
/-- The value of the wedge pairing on a pair of local sections over the same object is their
product. -/
theorem wedgeHom_eval (U : C) (x : (E.piece i).val.obj (op U)) (y : (E.piece j).val.obj (op U)) :
    ((wedgeHom E i j).val.app (op U) x).app (op (Over.mk (𝟙 U))) y =
      (E.mul i j).app (op U) x y := by
  change (E.mul i j).app (op U) ((E.piece i).val.map (𝟙 U).op x) y = _
  refine congrArg (fun z => (E.mul i j).app (op U) z y) ?_
  rw [op_id, PresheafOfModules.map_id]
  rfl

/-- Restricting a free sheaf of modules along an arrow of the site gives the free sheaf of modules
on the same index type. -/
noncomputable def overMapFreeIso {X Y : C} (g : X ⟶ Y) (I : Type u)
    [HasWeakSheafify (J.over X) AddCommGrpCat.{u}]
    [(J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasWeakSheafify (J.over Y) AddCommGrpCat.{u}]
    [(J.over Y).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (_root_.SheafOfModules.overMap (toRingCat J Osharp) g).obj
        (_root_.SheafOfModules.free (R := (toRingCat J Osharp).over Y) I) ≅
      _root_.SheafOfModules.free (R := (toRingCat J Osharp).over X) I :=
  haveI := Stacks.SheafOfModules.overMap_preservesColimits.{u, u, u, u} (toRingCat J Osharp) g
  PreservesCoproduct.iso (_root_.SheafOfModules.overMap (toRingCat J Osharp) g)
      (fun _ : I => _root_.SheafOfModules.unit ((toRingCat J Osharp).over Y)) ≪≫
    Sigma.mapIso fun _ => _root_.SheafOfModules.overMapUnitIso g

/-- **For a sheaf of modules `F` locally free of rank `a + b`, the wedge pairing identifies `⋀ᵃ F`
with `SheafHom(⋀ᵇ F, ⋀ᵃ⁺ᵇ F)`.** Here `E` is any exterior algebra of `F`.

Invertibility is local (`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop`): over an
object `W` mapping to a member of a trivialising covering, `F|_W` is free of rank `a + b`, and on
sections over `W` the wedge pairing is the bijection `bijective_mulSection_over`. -/
theorem isIso_wedgeHom [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
    {F : _root_.SheafOfModules.{u} (toRingCat J Osharp)} {gen : F ⟶ E.piece 1}
    (hE : IsExteriorAlgebra E gen) (a b : ℕ)
    [hF : _root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F (a + b)] :
    IsIso (wedgeHom E (a : ℤ) (b : ℤ)) := by
  classical
  obtain ⟨q, hq, hr⟩ := hF.exists_isFiniteLocallyFreeOfRankData
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_coversTop q.coversTop _
    fun k W g => ?_
  have : IsIso (q.generators k).π := hq.isIso k
  let I := (q.generators k).I
  let eW : F.over W ≅ _root_.SheafOfModules.free (R := (toRingCat J Osharp).over W) I :=
    ((_root_.SheafOfModules.overFunctorMap (toRingCat J Osharp) g).app F).symm ≪≫
      (_root_.SheafOfModules.overMap (toRingCat J Osharp) g).mapIso
        (asIso (q.generators k).π).symm ≪≫ overMapFreeIso g I
  let _ : LinearOrder I := IsWellOrder.linearOrder WellOrderingRel
  let _ : Fintype I := Fintype.ofEquiv _ (hr k).some.symm
  have hcard : a + b = Fintype.card I := by
    rw [Fintype.card_congr (hr k).some, Fintype.card_fin]
  have hb := bijective_mulSection_over W hE I eW hcard
  have hval : Function.Bijective (fun φ : (E.over W).piece (b : ℤ) ⟶
      (E.over W).piece ((a : ℤ) + (b : ℤ)) => φ.val) :=
    ⟨fun _ _ h => _root_.SheafOfModules.Hom.ext h, fun φ => ⟨⟨φ⟩, rfl⟩⟩
  rw [ConcreteCategory.isIso_iff_bijective]
  exact (show Function.Bijective ((fun φ : (E.over W).piece (b : ℤ) ⟶
      (E.over W).piece ((a : ℤ) + (b : ℤ)) => φ.val) ∘
        mulSection (Over.isTerminalMkId W) (E.over W) (a : ℤ) (b : ℤ)) from hval.comp hb)

end Global

end Stacks.SheafOfModules.WedgeDuality

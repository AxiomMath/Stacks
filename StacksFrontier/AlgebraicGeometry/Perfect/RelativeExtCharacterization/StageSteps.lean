module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExtCharacterization.Setup

/-!
# The steps of the stagewise identification of [Stacks, Tag 0DJV]

For `f : X ⟶ S`, `E` in `D(𝒪_X)` and a perfect `P` in `D(𝒪_X)` with `M = Rf_*R𝓗om(P, E)` perfect,
the identification `Hom(M^∨, N) ⟶ Hom(P, E ⊗^L Lf^*N)` of `StageIdentification` is a composite
of five maps, each natural in `N` and in `P`:

* `baseStep`: `Hom(M^∨, N) ≃ Hom(𝒪_S, M ⊗^L N)` ([Stacks, Tags 08DI, 0BYS, 08DQ]);
* `pfStep`: composition with the projection formula map
  `Rf_*R𝓗om(P, E) ⊗^L N ⟶ Rf_*(R𝓗om(P, E) ⊗^L Lf^*N)` ([Stacks, Tag 0B53]), bijective when that
  map is invertible ([Stacks, Tag 08EU]);
* the adjunction `Lf^* ⊣ Rf_*`;
* `targetIso`: `R𝓗om(P, E) ⊗^L Y ≅ R𝓗om(P, E ⊗^L Y)` for a perfect `P` ([Stacks, Tag 0ATN]);
* `finalStep`: `Hom(Lf^*𝒪_S, R𝓗om(P, W)) ≃ Hom(P, W)` ([Stacks, Tag 08DI]).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf structureSheafRing CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

namespace Stacks.AlgebraicGeometry.RelativeExtCharacterization

open Stacks.SheafOfModules Stacks.AlgebraicGeometry.RelativeDerivedHomDual

attribute [local instance] derivedMonoidalStructure derivedSymmetricStructure

section TensorHom

variable {Z : Scheme.{u}}

/-- [Stacks, Tag 08DI] read backwards, natural in the target. -/
theorem tensorHomEquiv_symm_comp (A B : DStd Z) {N N' : DStd Z} (m : N ⟶ N') (y : A ⊗ B ⟶ N) :
    (derivedSheafHomTensorEquiv Z.sheaf A B N').symm (y ≫ m) =
      (derivedSheafHomTensorEquiv Z.sheaf A B N).symm y ≫ rhomMapR B m := by
  rw [AddEquiv.symm_apply_eq, derivedSheafHomTensorEquiv_naturality_target,
    AddEquiv.apply_symm_apply]

/-- [Stacks, Tag 08DI] read backwards, dinatural in the internal Hom variable. -/
theorem tensorHomEquiv_symm_whisker (A : DStd Z) {B B' : DStd Z} (v : B' ⟶ B) (N : DStd Z)
    (y : A ⊗ B ⟶ N) :
    (derivedSheafHomTensorEquiv Z.sheaf A B' N).symm (A ◁ v ≫ y) =
      (derivedSheafHomTensorEquiv Z.sheaf A B N).symm y ≫ rhomMapL v N := by
  rw [AddEquiv.symm_apply_eq, ← derivedSheafHomTensorEquiv_dinaturality,
    AddEquiv.apply_symm_apply]
  rfl

end TensorHom

section BaseSide

variable {S : Scheme.{u}}

/-- The base step `Hom(M^∨, N) ⟶ Hom(𝒪, M ⊗ N)`. -/
def baseStep (M : DStd S) (hM : IsPerfectSite M) (N : DStd S)
    (x : rhom M (unitObj S) ⟶ N) : unitObj S ⟶ M ⊗ N :=
  (derivedSheafHomTensorEquiv S.sheaf (unitObj S) _ N).symm ((λ_ _).hom ≫ x) ≫
    (dualHomIso M hM N).hom ≫ (β_ N M).hom

/-- For a perfect `M`, the base step `baseStep M hM N` is bijective. -/
theorem baseStep_bijective (M : DStd S) (hM : IsPerfectSite M) (N : DStd S) :
    Function.Bijective (baseStep M hM N) := by
  have h := ((bijective_comp_iso (dualHomIso M hM N ≪≫ β_ N M)).comp
    (derivedSheafHomTensorEquiv S.sheaf (unitObj S) (rhom M (unitObj S)) N).symm.bijective).comp
    (bijective_iso_comp (Y := N) (λ_ (rhom M (unitObj S))))
  convert h using 1
  funext x
  simp [baseStep]

/-- The base step is natural in `N`: it carries `x ≫ g` to `baseStep M hM N x ≫ M ◁ g`. -/
theorem baseStep_naturality_right (M : DStd S) (hM : IsPerfectSite M) {N N' : DStd S}
    (g : N ⟶ N') (x : rhom M (unitObj S) ⟶ N) :
    baseStep M hM N' (x ≫ g) = baseStep M hM N x ≫ M ◁ g := by
  simp only [baseStep]
  rw [← Category.assoc _ x g, tensorHomEquiv_symm_comp, Category.assoc,
    ← Category.assoc (rhomMapR _ g), dualHomIso_naturality_right, Category.assoc,
    Category.assoc, BraidedCategory.braiding_naturality_left]
  simp only [Category.assoc]

/-- The base step is natural in the perfect complex `M`, with respect to `m : M' ⟶ M`. -/
theorem baseStep_naturality_left {M M' : DStd S} (m : M' ⟶ M) (hM : IsPerfectSite M)
    (hM' : IsPerfectSite M') (N : DStd S) (x : rhom M' (unitObj S) ⟶ N) :
    baseStep M hM N (rhomMapL m (unitObj S) ≫ x) = baseStep M' hM' N x ≫ m ▷ N := by
  have hl : (λ_ (rhom M (unitObj S))).hom ≫ rhomMapL m (unitObj S) ≫ x =
      unitObj S ◁ rhomMapL m (unitObj S) ≫ (λ_ (rhom M' (unitObj S))).hom ≫ x := by
    simp only [← Category.assoc]
    congr 1
    exact (leftUnitor_naturality _).symm
  simp only [baseStep]
  rw [hl, tensorHomEquiv_symm_whisker,
    Category.assoc, ← Category.assoc (rhomMapL _ N), dualHomIso_naturality_left m hM hM',
    Category.assoc, Category.assoc, BraidedCategory.braiding_naturality_right]
  simp only [Category.assoc]

end BaseSide

section ProjectionStep

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The projection formula map `Rf_*A ⊗ N ⟶ Rf_*(A ⊗ Lf^*N)` of [Stacks, Tag 0B53]. -/
abbrev pfMap (A : DStd X) (N : DStd S) :
    ((tensorPF S).obj ((pushStd f).obj A)).obj N ⟶
      (pushStd f).obj (((tensorPF X).obj A).obj ((pullStd f).obj N)) :=
  Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap f.toLRSHom.toShHom A N

/-- The projection formula map `pfMap f A N` is natural in `A`. -/
theorem pfMap_natural_left {A A' : DStd X} (a : A' ⟶ A) (N : DStd S) :
    ((tensorPF S).map ((pushStd f).map a)).app N ≫ pfMap f A N =
      pfMap f A' N ≫ (pushStd f).map (((tensorPF X).map a).app ((pullStd f).obj N)) :=
  Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_left
    f.toLRSHom.toShHom a N

/-- The projection formula map `pfMap f A N` is natural in `N`. -/
theorem pfMap_natural_right (A : DStd X) {N N' : DStd S} (g : N ⟶ N') :
    ((tensorPF S).obj ((pushStd f).obj A)).map g ≫ pfMap f A N' =
      pfMap f A N ≫ (pushStd f).map (((tensorPF X).obj A).map ((pullStd f).map g)) :=
  Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap_natural_right
    f.toLRSHom.toShHom A g

/-- The components of `(tensorPFIso Z).inv` are natural in the second tensor factor. -/
@[reassoc]
theorem tensorPFIso_inv_natural_right (Z : Scheme.{u}) (A : DStd Z) {N N' : DStd Z}
    (g : N ⟶ N') :
    A ◁ g ≫ ((tensorPFIso Z).inv.app A).app N' =
      ((tensorPFIso Z).inv.app A).app N ≫ ((tensorPF Z).obj A).map g :=
  ((tensorPFIso Z).inv.app A).naturality g

/-- The components of `(tensorPFIso Z).inv` are natural in the first tensor factor. -/
@[reassoc]
theorem tensorPFIso_inv_natural_left (Z : Scheme.{u}) {A A' : DStd Z} (a : A' ⟶ A)
    (N : DStd Z) :
    a ▷ N ≫ ((tensorPFIso Z).inv.app A).app N =
      ((tensorPFIso Z).inv.app A').app N ≫ ((tensorPF Z).map a).app N :=
  congrArg (fun t ↦ t.app N) ((tensorPFIso Z).inv.naturality a)

/-- The components of `(tensorPFIso Z).hom` are natural in the second tensor factor. -/
@[reassoc]
theorem tensorPFIso_hom_natural_right (Z : Scheme.{u}) (A : DStd Z) {N N' : DStd Z}
    (g : N ⟶ N') :
    ((tensorPF Z).obj A).map g ≫ ((tensorPFIso Z).hom.app A).app N' =
      ((tensorPFIso Z).hom.app A).app N ≫ A ◁ g :=
  ((tensorPFIso Z).hom.app A).naturality g

/-- The components of `(tensorPFIso Z).hom` are natural in the first tensor factor. -/
@[reassoc]
theorem tensorPFIso_hom_natural_left (Z : Scheme.{u}) {A A' : DStd Z} (a : A' ⟶ A)
    (N : DStd Z) :
    ((tensorPF Z).map a).app N ≫ ((tensorPFIso Z).hom.app A).app N =
      ((tensorPFIso Z).hom.app A').app N ≫ a ▷ N :=
  congrArg (fun t ↦ t.app N) ((tensorPFIso Z).hom.naturality a)

/-- The projection step `Hom(𝒪, Rf_*A ⊗ N) ⟶ Hom(𝒪, Rf_*(A ⊗ Lf^*N))`. -/
def pfStep (A : DStd X) (N : DStd S) (y : unitObj S ⟶ (pushStd f).obj A ⊗ N) :
    unitObj S ⟶ (pushStd f).obj (((tensorPF X).obj A).obj ((pullStd f).obj N)) :=
  y ≫ ((tensorPFIso S).inv.app ((pushStd f).obj A)).app N ≫ pfMap f A N

/-- The projection step `pfStep f A N` is bijective when `pfMap f A N` is an isomorphism. -/
theorem pfStep_bijective (A : DStd X) (N : DStd S) (h : IsIso (pfMap f A N)) :
    Function.Bijective (pfStep f A N) := by
  convert bijective_comp_iso (Y := unitObj S)
    (((tensorPFIso S).app ((pushStd f).obj A)).symm.app N ≪≫ asIso (pfMap f A N)) using 1
  funext y
  rfl

/-- The projection step `pfStep f A N` is natural in `N`. -/
theorem pfStep_naturality_right (A : DStd X) {N N' : DStd S} (g : N ⟶ N')
    (y : unitObj S ⟶ (pushStd f).obj A ⊗ N) :
    pfStep f A N' (y ≫ (pushStd f).obj A ◁ g) =
      pfStep f A N y ≫ (pushStd f).map (((tensorPF X).obj A).map ((pullStd f).map g)) := by
  simp only [pfStep, Category.assoc]
  rw [tensorPFIso_inv_natural_right_assoc, pfMap_natural_right]

/-- The projection step `pfStep f A N` is natural in `A`. -/
theorem pfStep_naturality_left {A A' : DStd X} (a : A' ⟶ A) (N : DStd S)
    (y : unitObj S ⟶ (pushStd f).obj A' ⊗ N) :
    pfStep f A N (y ≫ (pushStd f).map a ▷ N) =
      pfStep f A' N y ≫ (pushStd f).map (((tensorPF X).map a).app ((pullStd f).obj N)) := by
  simp only [pfStep, Category.assoc]
  rw [tensorPFIso_inv_natural_left_assoc, pfMap_natural_left]

end ProjectionStep

section TargetSide

variable {X : Scheme.{u}}

/-- `R𝓗om(P, E) ⊗ Y ≅ R𝓗om(P, E ⊗ Y)` for a perfect `P`, in the tensor product of the projection
formula: the comparison of the two derived tensor products, the symmetry, the diagonal of
[Stacks, Tag 0BYS] and the symmetry again. -/
def targetIso (P : DStd X) (hP : IsPerfectSite P) (E Y : DStd X) :
    ((tensorPF X).obj (rhom P E)).obj Y ≅ rhom P (E ⊗ Y) :=
  haveI := isIso_diag Y E P hP
  ((tensorPFIso X).app (rhom P E)).app Y ≪≫ β_ (rhom P E) Y ≪≫ asIso (diag Y E P) ≪≫
    ((derivedSheafHom X.sheaf).obj (op P)).mapIso (β_ Y E)

/-- The forward map of `targetIso P hP E Y` as the composite of its four constituents. -/
theorem targetIso_hom (P : DStd X) (hP : IsPerfectSite P) (E Y : DStd X) :
    (targetIso P hP E Y).hom = ((tensorPFIso X).hom.app (rhom P E)).app Y ≫
      (β_ (rhom P E) Y).hom ≫ diag Y E P ≫ rhomMapR P (β_ Y E).hom := rfl

/-- The isomorphism `targetIso P hP E Y` is natural in `Y`. -/
theorem targetIso_naturality_right (P : DStd X) (hP : IsPerfectSite P) (E : DStd X)
    {Y Y' : DStd X} (y : Y ⟶ Y') :
    ((tensorPF X).obj (rhom P E)).map y ≫ (targetIso P hP E Y').hom =
      (targetIso P hP E Y).hom ≫ rhomMapR P (E ◁ y) := by
  rw [targetIso_hom, targetIso_hom, tensorPFIso_hom_natural_right_assoc,
    BraidedCategory.braiding_naturality_right_assoc, diag_natural_left_assoc]
  simp only [Category.assoc, ← Functor.map_comp, BraidedCategory.braiding_naturality_left]

/-- The isomorphism `targetIso P hP E Y` is natural in the perfect complex `P`. -/
theorem targetIso_naturality_left {P P' : DStd X} (k : P ⟶ P') (hP : IsPerfectSite P)
    (hP' : IsPerfectSite P') (E Y : DStd X) :
    ((tensorPF X).map (rhomMapL k E)).app Y ≫ (targetIso P hP E Y).hom =
      (targetIso P' hP' E Y).hom ≫ rhomMapL k (E ⊗ Y) := by
  rw [targetIso_hom, targetIso_hom, tensorPFIso_hom_natural_left_assoc,
    BraidedCategory.braiding_naturality_left_assoc, diag_natural_hom_assoc]
  simp only [Category.assoc]
  congr 3
  exact (((derivedSheafHom X.sheaf).map k.op).naturality (β_ Y E).hom).symm

variable {S : Scheme.{u}} (f : X ⟶ S)

/-- The final step `Hom(Lf^*𝒪_S, R𝓗om(P, W)) ⟶ Hom(P, W)` of [Stacks, Tag 08DI]. -/
def finalStep (P W : DStd X) (w : (pullStd f).obj (unitObj S) ⟶ rhom P W) : P ⟶ W :=
  ((λ_ P).inv ≫ (pullbackUnitIso f).inv ▷ P) ≫
    derivedSheafHomTensorEquiv X.sheaf ((pullStd f).obj (unitObj S)) P W w

/-- The final step `finalStep f P W` is bijective. -/
theorem finalStep_bijective (P W : DStd X) : Function.Bijective (finalStep f P W) :=
  (bijective_iso_comp ((λ_ P).symm ≪≫ whiskerRightIso (pullbackUnitIso f).symm P)).comp
    (derivedSheafHomTensorEquiv X.sheaf ((pullStd f).obj (unitObj S)) P W).bijective

/-- The final step `finalStep f P W` is natural in `W`. -/
theorem finalStep_naturality_right (P : DStd X) {W W' : DStd X} (z : W ⟶ W')
    (w : (pullStd f).obj (unitObj S) ⟶ rhom P W) :
    finalStep f P W' (w ≫ rhomMapR P z) = finalStep f P W w ≫ z := by
  simp only [finalStep]
  rw [derivedSheafHomTensorEquiv_naturality_target]
  simp only [Category.assoc]

/-- The final step `finalStep f P W` is natural in `P`. -/
theorem finalStep_naturality_left {P P' : DStd X} (k : P ⟶ P') (W : DStd X)
    (w : (pullStd f).obj (unitObj S) ⟶ rhom P' W) :
    finalStep f P W (w ≫ rhomMapL k W) = k ≫ finalStep f P' W w := by
  simp only [finalStep]
  rw [← derivedSheafHomTensorEquiv_dinaturality]
  have h1 : (pullbackUnitIso f).inv ▷ P ≫
      ((derivedTensor X.sheaf).obj ((pullStd f).obj (unitObj S))).map k =
      unitObj X ◁ k ≫ (pullbackUnitIso f).inv ▷ P' := (whisker_exchange _ _).symm
  simp only [Category.assoc]
  have h2 : (λ_ P).inv ≫ unitObj X ◁ k = k ≫ (λ_ P').inv := (leftUnitor_inv_naturality k).symm
  rw [reassoc_of% h1, reassoc_of% h2]

end TargetSide

end Stacks.AlgebraicGeometry.RelativeExtCharacterization

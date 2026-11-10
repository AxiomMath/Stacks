module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteEquivalenceTransport
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeTopSectionsLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeModuleHomEquiv
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleLocalBijectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsTerminalChart
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineBaseTerminalChartIsomorphismDetection

/-!
# Sections over a terminal affine chart and their left adjoint

Let `Y` be an algebraic space over a scheme `S` of a big fppf site `B` and let `A` be a terminal
object of the small étale site of `Y` whose scheme is affine (an affine algebraic space has one,
`AlgebraicGeometry.Space.exists_isTerminal_isAffine_chart`). The sections over `A`,
`Γ(A, -) : Mod(𝒪_Y) ⥤ Mod(𝒪_Y(A))`, have a left adjoint `Φ` with invertible unit: `Φ M` is the
quasi-coherent module associated with `M` (Descent, Proposition 03DX, at the affine chart).

## Main definitions

* `AlgebraicGeometry.Space.affineChartTilde`: the functor `Φ`.
* `AlgebraicGeometry.Space.affineChartTildeAdjunction`: `Φ ⊣ Γ(A, -)`, with invertible unit
  `AlgebraicGeometry.Space.isIso_affineChartTildeAdjunction_unit`.

## Implementation notes

`Φ` is assembled from adjunctions already in the library: the tilde construction on the affine
scheme `T` of `A` (`tilde.adjunction`, through `T ≅ Spec Γ(T, ⊤)`), the associated module on the
small étale site of `T` (`AlgebraicGeometry.SmallEtale.associatedModuleAdjunction`, whose unit is
invertible on quasi-coherent modules), and the equivalence between the modules on `Y` and those on
the small étale site of `T` given by the terminal chart (`terminalChartModuleEquivalence`). The
right adjoint so obtained is identified with `Γ(A, -)` abstractly, without computing sections:
`SheafOfModules.adjointSectionsIso` shows that a right adjoint `G` of a functor `L` with
`L(R) ≅ 𝒪` is `Γ(A, -)` read through the ring isomorphism `R ≅ 𝒪(A)` which `L` induces
(`SheafOfModules.scalarRingEquiv`).

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 08H0](https://stacks.math.columbia.edu/tag/08H0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]

/-- Along an isomorphism of schemes the unit of `restrictFunctor f ⊣ pushforward f` is
invertible. -/
instance isIso_restrictAdjunction_unit_of_isIso :
    IsIso (restrictAdjunction f).unit := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ ?_
  rw [Hom.isIso_iff_isIso_app]
  intro U
  rw [restrictAdjunction_unit_app_app]
  have h : f ''ᵁ f ⁻¹ᵁ U = U := by
    rw [Hom.image_preimage_eq_opensRange_inf]
    simp [Hom.opensRange_of_isIso]
  rw [show homOfLE (f.image_preimage_le U) = eqToHom h from rfl]
  exact Functor.map_isIso M.presheaf _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable (T : Scheme.{u}) [IsAffine T]

/-- **The global sections of an affine scheme have a left adjoint with invertible unit**: the
tilde construction, read on `T` through `T ≅ Spec Γ(T, ⊤)`. -/
def affineSchemeSectionsAdjunction :
    (tilde.functor Γ(T, ⊤) ⋙ Scheme.Modules.restrictFunctor T.isoSpec.hom) ⊣
      (Scheme.Modules.pushforward T.isoSpec.hom ⋙ moduleSpecΓFunctor) :=
  tilde.adjunction.comp (Scheme.Modules.restrictAdjunction T.isoSpec.hom)

/-- The unit of `affineSchemeSectionsAdjunction` is invertible. -/
instance isIso_affineSchemeSectionsAdjunction_unit :
    IsIso (affineSchemeSectionsAdjunction T).unit := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ ?_
  simp only [affineSchemeSectionsAdjunction, Adjunction.comp_unit_app]
  infer_instance

end AlgebraicGeometry

namespace SheafOfModules

variable {C : Type*} [Category* C] {J : GrothendieckTopology C} {O : Sheaf J RingCat.{u}}
  {A : C} (hA : IsTerminal A)

/-- Morphisms out of the unit module are the sections over a terminal object. -/
def unitHomEquivOfIsTerminal (F : SheafOfModules.{u} O) :
    (SheafOfModules.unit O ⟶ F) ≃ F.val.obj (op A) :=
  F.unitHomEquiv.trans (PresheafOfModules.sectionsEquivObjOfIsTerminal F.val hA)

/-- `unitHomEquivOfIsTerminal` sends a morphism `φ` to the value of `φ` at `1` over `A`. -/
lemma unitHomEquivOfIsTerminal_apply (F : SheafOfModules.{u} O) (φ : SheafOfModules.unit O ⟶ F) :
    unitHomEquivOfIsTerminal hA F φ = φ.val.app (op A) (1 : O.obj.obj (op A)) := rfl

/-- The value at `1` over `A` of an endomorphism of the unit module, as an element of the ring
of sections of `O` over `A`. -/
def unitEndValue (ψ : SheafOfModules.unit O ⟶ SheafOfModules.unit O) : O.obj.obj (op A) :=
  ψ.val.app (op A) (1 : O.obj.obj (op A))

/-- Precomposing with an endomorphism of the unit module multiplies the section by the value of
that endomorphism at `1`. -/
lemma comp_val_app_one (F : SheafOfModules.{u} O)
    (ψ : SheafOfModules.unit O ⟶ SheafOfModules.unit O) (φ : SheafOfModules.unit O ⟶ F) :
    (ψ ≫ φ).val.app (op A) (1 : O.obj.obj (op A)) =
      unitEndValue (A := A) ψ • φ.val.app (op A) (1 : O.obj.obj (op A)) := by
  have h : ψ.val.app (op A) (1 : O.obj.obj (op A)) =
      unitEndValue (A := A) ψ • (1 : O.obj.obj (op A)) :=
    (mul_one (unitEndValue (A := A) ψ)).symm
  change φ.val.app (op A) (ψ.val.app (op A) (1 : O.obj.obj (op A))) = _
  rw [h]
  exact (φ.val.app (op A)).hom.map_smul _ _

/-- The value at `1` of an endomorphism of the unit module is its image under
`unitHomEquivOfIsTerminal`. -/
lemma unitEndValue_eq (ψ : SheafOfModules.unit O ⟶ SheafOfModules.unit O) :
    unitEndValue (A := A) ψ = unitHomEquivOfIsTerminal hA (SheafOfModules.unit O) ψ := rfl

/-- The sections over an object, at module universe `u`. -/
abbrev terminalSections (A : C) : SheafOfModules.{u} O ⥤ ModuleCat.{u} (O.obj.obj (op A)) :=
  SheafOfModules.evaluation O (op A)

section Scalars

variable {R : Type u} [CommRing R] {L : ModuleCat.{u} R ⥤ SheafOfModules.{u} O}
  {G : SheafOfModules.{u} O ⥤ ModuleCat.{u} R} (adj : L ⊣ G)
  (e₀ : L.obj (ModuleCat.of R R) ≅ SheafOfModules.unit O)

/-- Multiplication by a scalar, as an endomorphism of the free module of rank one. -/
abbrev scalarEnd (r : R) : ModuleCat.of R R ⟶ ModuleCat.of R R :=
  ModuleCat.ofHom (LinearMap.lsmul R R r)

/-- Multiplication by `1` is the identity. -/
lemma scalarEnd_one : scalarEnd (1 : R) = 𝟙 _ := by
  ext; simp

/-- Multiplication by `r * s` is multiplication by `s` followed by multiplication by `r`. -/
lemma scalarEnd_mul (r s : R) : scalarEnd (r * s) = scalarEnd s ≫ scalarEnd r := by
  ext; simp

/-- Multiplication by `0` is the zero morphism. -/
lemma scalarEnd_zero : scalarEnd (0 : R) = 0 := by
  ext; simp

/-- Multiplication by `r + s` is the sum of multiplication by `r` and by `s`. -/
lemma scalarEnd_add (r s : R) : scalarEnd (r + s) = scalarEnd r + scalarEnd s := by
  ext; simp

/-- The endomorphism of the unit module which `L` attaches to a scalar, through `e₀`. -/
def unitScalarEnd (r : R) : SheafOfModules.unit O ⟶ SheafOfModules.unit O :=
  e₀.inv ≫ L.map (scalarEnd r) ≫ e₀.hom

include adj in
/-- A left adjoint `L : ModuleCat R ⥤ SheafOfModules O` is additive. -/
lemma additive_of_isLeftAdjoint : L.Additive := by
  have : PreservesColimitsOfShape (Discrete WalkingPair) L := by
    have := adj.leftAdjoint_preservesColimits
    infer_instance
  have : L.IsLeftAdjoint := adj.isLeftAdjoint
  have : L.PreservesZeroMorphisms := Functor.preservesZeroMorphisms_of_isLeftAdjoint L
  have : PreservesBinaryBiproducts L := preservesBinaryBiproducts_of_preservesBinaryCoproducts L
  exact Functor.additive_of_preservesBinaryBiproducts L

include hA adj in
/-- **The ring homomorphism `R → O(A)` determined by a left adjoint `L` with `L(R) ≅ O`.** -/
def scalarRingHom : R →+* O.obj.obj (op A) where
  toFun r := unitEndValue (A := A) (unitScalarEnd e₀ r)
  map_one' := by
    simp only [unitScalarEnd, scalarEnd_one, CategoryTheory.Functor.map_id, Category.id_comp,
      Iso.inv_hom_id]
    rfl
  map_mul' r s := by
    rw [mul_comm r s, show unitScalarEnd e₀ (s * r) = unitScalarEnd e₀ r ≫ unitScalarEnd e₀ s by
      simp only [unitScalarEnd, scalarEnd_mul, Functor.map_comp, Category.assoc,
        Iso.hom_inv_id_assoc]]
    rw [unitEndValue_eq hA, unitHomEquivOfIsTerminal_apply hA]
    exact comp_val_app_one (A := A) _ _ _
  map_zero' := by
    have : L.Additive := additive_of_isLeftAdjoint adj
    simp only [unitScalarEnd, scalarEnd_zero, Functor.map_zero, Limits.zero_comp,
      Limits.comp_zero]
    rfl
  map_add' r s := by
    have : L.Additive := additive_of_isLeftAdjoint adj
    simp only [unitScalarEnd, scalarEnd_add, Functor.map_add, Preadditive.add_comp,
      Preadditive.comp_add]
    rfl

/-- `scalarRingHom` sends `r` to the value at `1` of `unitScalarEnd e₀ r`. -/
lemma scalarRingHom_apply (r : R) :
    scalarRingHom hA adj e₀ r = unitEndValue (A := A) (unitScalarEnd e₀ r) := rfl

/-- Every endomorphism of the free module of rank one is multiplication by its value at `1`. -/
lemma scalarEnd_hom_one_eq (f : ModuleCat.of R R ⟶ ModuleCat.of R R) :
    f = scalarEnd (f.hom (1 : R)) := by
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  simp

/-- **The scalar ring homomorphism is bijective** when the unit of `L ⊣ G` is invertible. -/
lemma bijective_scalarRingHom [IsIso adj.unit] : Function.Bijective (scalarRingHom hA adj e₀) := by
  let hL := adj.fullyFaithfulLOfIsIsoUnit
  constructor
  · intro r s h
    rw [scalarRingHom_apply, scalarRingHom_apply, unitEndValue_eq hA, unitEndValue_eq hA] at h
    have h₂ : L.map (scalarEnd r) = L.map (scalarEnd s) := by
      simpa [unitScalarEnd] using congrArg (fun φ ↦ e₀.hom ≫ φ ≫ e₀.inv)
        ((unitHomEquivOfIsTerminal hA (SheafOfModules.unit O)).injective h)
    simpa using congrArg (fun f : ModuleCat.of R R ⟶ ModuleCat.of R R ↦ f.hom (1 : R))
      (hL.map_injective h₂)
  · intro t
    let ψ := (unitHomEquivOfIsTerminal hA (SheafOfModules.unit O)).symm t
    let f := hL.preimage (e₀.hom ≫ ψ ≫ e₀.inv)
    refine ⟨f.hom (1 : R), ?_⟩
    rw [scalarRingHom_apply, unitScalarEnd, ← scalarEnd_hom_one_eq f, unitEndValue_eq hA,
      show e₀.inv ≫ L.map f ≫ e₀.hom = ψ by simp [f]]
    exact (unitHomEquivOfIsTerminal hA (SheafOfModules.unit O)).apply_symm_apply t

/-- The scalar ring homomorphism as a ring isomorphism. -/
noncomputable def scalarRingEquiv [IsIso adj.unit] : R ≃+* O.obj.obj (op A) :=
  RingEquiv.ofBijective (scalarRingHom hA adj e₀) (bijective_scalarRingHom hA adj e₀)

/-- The sections of `G F` are the sections of `F` over the terminal object `A`. -/
def adjointSectionsEquiv (F : SheafOfModules.{u} O) : G.obj F ≃ F.val.obj (op A) where
  toFun x := unitHomEquivOfIsTerminal hA F (e₀.inv ≫ (adj.homEquiv _ _).symm
    (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x)))
  invFun y := ((adj.homEquiv _ _) (e₀.hom ≫ (unitHomEquivOfIsTerminal hA F).symm y)).hom 1
  left_inv x := by simp
  right_inv y := by
    have h : ModuleCat.ofHom (LinearMap.toSpanSingleton R _
        (((adj.homEquiv _ _) (e₀.hom ≫ (unitHomEquivOfIsTerminal hA F).symm y)).hom 1)) =
        (adj.homEquiv _ _) (e₀.hom ≫ (unitHomEquivOfIsTerminal hA F).symm y) := by
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      rw [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, ← LinearMap.map_smul,
        smul_eq_mul, mul_one]
    simp only [h, Equiv.symm_apply_apply, Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

/-- `adjointSectionsEquiv` sends `x` to the value at `1` over `A` of the morphism out of the unit
module adjoint to `r ↦ r • x`. -/
lemma adjointSectionsEquiv_apply (F : SheafOfModules.{u} O) (x : G.obj F) :
    adjointSectionsEquiv hA adj e₀ F x = (e₀.inv ≫ (adj.homEquiv _ _).symm
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x))).val.app (op A) (1 : O.obj.obj (op A)) :=
  rfl

/-- `adjointSectionsEquiv` is semilinear along `scalarRingHom`. -/
lemma adjointSectionsEquiv_smul (F : SheafOfModules.{u} O) (r : R) (x : G.obj F) :
    adjointSectionsEquiv hA adj e₀ F (r • x) =
      scalarRingHom hA adj e₀ r • adjointSectionsEquiv hA adj e₀ F x := by
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (r • x)) =
      scalarEnd r ≫ ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
    simp [mul_smul, smul_comm y r x]
  rw [adjointSectionsEquiv_apply, adjointSectionsEquiv_apply, h,
    Adjunction.homEquiv_naturality_left_symm]
  have h' : e₀.inv ≫ L.map (scalarEnd r) ≫ (adj.homEquiv _ _).symm
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x)) =
      unitScalarEnd e₀ r ≫ (e₀.inv ≫ (adj.homEquiv _ _).symm
        (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x))) := by
    simp [unitScalarEnd]
  rw [h', comp_val_app_one (A := A)]
  rfl

/-- `adjointSectionsEquiv` is natural in the module. -/
lemma adjointSectionsEquiv_naturality {F F' : SheafOfModules.{u} O} (f : F ⟶ F') (x : G.obj F) :
    adjointSectionsEquiv hA adj e₀ F' ((G.map f).hom x) =
      f.val.app (op A) (adjointSectionsEquiv hA adj e₀ F x) := by
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton R _ ((G.map f).hom x)) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x) ≫ G.map f := by
    refine ModuleCat.hom_ext (LinearMap.ext fun y ↦ ?_)
    simp
  rw [adjointSectionsEquiv_apply, adjointSectionsEquiv_apply, h,
    Adjunction.homEquiv_naturality_right_symm]
  rfl

/-- For an additive left adjoint, the inverse of the adjunction bijection on morphisms is
additive. -/
lemma homEquiv_symm_add [L.Additive] {N : ModuleCat.{u} R} {F : SheafOfModules.{u} O}
    (f g : N ⟶ G.obj F) :
    (adj.homEquiv _ _).symm (f + g) = (adj.homEquiv _ _).symm f + (adj.homEquiv _ _).symm g := by
  simp only [Adjunction.homEquiv_counit, Functor.map_add, Preadditive.add_comp]

/-- `adjointSectionsEquiv` is additive. -/
lemma adjointSectionsEquiv_add (F : SheafOfModules.{u} O) (x y : G.obj F) :
    adjointSectionsEquiv hA adj e₀ F (x + y) =
      adjointSectionsEquiv hA adj e₀ F x + adjointSectionsEquiv hA adj e₀ F y := by
  have : L.Additive := additive_of_isLeftAdjoint adj
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton R _ (x + y)) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x) +
        ModuleCat.ofHom (LinearMap.toSpanSingleton R _ y) := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z ↦ ?_)
    simp
  rw [adjointSectionsEquiv_apply, adjointSectionsEquiv_apply, adjointSectionsEquiv_apply, h,
    homEquiv_symm_add adj, Preadditive.comp_add]
  rfl

/-- The comparison `G F ≅ θ^* Γ(A, F)` at one object. -/
def adjointSectionsIsoApp (F : SheafOfModules.{u} O) :
    G.obj F ≅ (ModuleCat.restrictScalars.{u} (scalarRingHom hA adj e₀)).obj
      ((terminalSections (O := O) A).obj F) :=
  (AddEquiv.toLinearEquiv (M := ↑(G.obj F))
    (M₂ := ↑((ModuleCat.restrictScalars.{u} (scalarRingHom hA adj e₀)).obj
      ((terminalSections (O := O) A).obj F)))
    { toEquiv := adjointSectionsEquiv hA adj e₀ F
      map_add' := adjointSectionsEquiv_add hA adj e₀ F }
    (adjointSectionsEquiv_smul hA adj e₀ F)).toModuleIso

/-- **The right adjoint `G` is the sections over `A`**, read over `R` through the scalar ring
homomorphism. -/
def adjointSectionsIso :
    G ≅ terminalSections (O := O) A ⋙
      ModuleCat.restrictScalars.{u} (scalarRingHom hA adj e₀) :=
  NatIso.ofComponents (adjointSectionsIsoApp hA adj e₀)
    (fun f ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦
      adjointSectionsEquiv_naturality hA adj e₀ f x))

variable [IsIso adj.unit]

/-- **The left adjoint of the sections over a terminal object**, as a functor out of the modules
over the ring of sections of `O` over that object. -/
def terminalSectionsLeftAdjoint :
    ModuleCat.{u} (O.obj.obj (op A)) ⥤ SheafOfModules.{u} O :=
  ModuleCat.restrictScalars (scalarRingEquiv hA adj e₀).toRingHom ⋙ L

/-- **`terminalSectionsLeftAdjoint ⊣ Γ(A, -)`.** -/
def terminalSectionsAdjunction :
    terminalSectionsLeftAdjoint hA adj e₀ ⊣ terminalSections (O := O) A :=
  ((ModuleCat.restrictScalarsEquivalenceOfRingEquiv (scalarRingEquiv hA adj e₀)).toAdjunction.comp
      adj).ofNatIsoRight
    (Functor.isoWhiskerRight (adjointSectionsIso hA adj e₀) _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _
        (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
          (scalarRingEquiv hA adj e₀)).unitIso.symm ≪≫
      Functor.rightUnitor _)

/-- The unit of `terminalSectionsAdjunction` is invertible. -/
instance isIso_terminalSectionsAdjunction_unit :
    IsIso (terminalSectionsAdjunction hA adj e₀).unit := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun N ↦ ?_
  simp only [terminalSectionsAdjunction, Adjunction.ofNatIsoRight, NatTrans.comp_app]
  have h1 : IsIso (((ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (scalarRingEquiv hA adj e₀)).toAdjunction.comp adj).unit.app N) := by
    rw [Adjunction.comp_unit_app, Equivalence.toAdjunction_unit]
    infer_instance
  refine IsIso.comp_isIso' h1 ?_
  rw [Functor.whiskerLeft_app]
  exact NatIso.isIso_app_of_isIso _ _

end Scalars

end SheafOfModules

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (Y : AlgebraicSpaces B S hS) {A : SmallEtale B S hS Y.1}

/-- The inverse of the equivalence `Over A ≌ C` at a terminal object is cocontinuous. -/
instance isCocontinuous_equivalenceOfIsTerminal_inverse (hA : IsTerminal A) :
    (Over.equivalenceOfIsTerminal hA).inverse.IsCocontinuous
      (SmallEtale.topology B S hS Y.1) ((SmallEtale.topology B S hS Y.1).over A) where
  cover_lift {Z} T hT := by
    rw [GrothendieckTopology.mem_over_iff] at hT
    refine (SmallEtale.topology B S hS Y.1).superset_covering (fun W g hg ↦ ?_) hT
    have hg' := (Sieve.overEquiv_iff
      (Y := (Over.equivalenceOfIsTerminal hA).inverse.obj Z) T (Z := W) g).1 hg
    have h := T.downward_closed hg' (Over.homMk
      (U := (Over.equivalenceOfIsTerminal hA).inverse.obj W) (V := Over.mk (g ≫ hA.from Z))
      (𝟙 W) (hA.hom_ext _ _))
    change T _
    convert h using 1
    exact Over.OverMorphism.ext (Category.id_comp g).symm

/-- The functor of the equivalence `Over A ≌ C` at a terminal object is continuous. -/
instance isContinuous_equivalenceOfIsTerminal_functor (hA : IsTerminal A) :
    (Over.equivalenceOfIsTerminal hA).functor.IsContinuous
      ((SmallEtale.topology B S hS Y.1).over A) (SmallEtale.topology B S hS Y.1) :=
  inferInstanceAs ((Over.forget A).IsContinuous _ _)

/-- The inverse of the equivalence `Over A ≌ C` at a terminal object is continuous. -/
instance isContinuous_equivalenceOfIsTerminal_inverse (hA : IsTerminal A) :
    (Over.equivalenceOfIsTerminal hA).inverse.IsContinuous
      (SmallEtale.topology B S hS Y.1) ((SmallEtale.topology B S hS Y.1).over A) := by
  have : (Over.equivalenceOfIsTerminal hA).functor.IsCocontinuous
      ((SmallEtale.topology B S hS Y.1).over A) (SmallEtale.topology B S hS Y.1) :=
    inferInstanceAs ((Over.forget A).IsCocontinuous _ _)
  have := Equivalence.isDenseSubsite_inverse_of_isCocontinuous
    ((SmallEtale.topology B S hS Y.1).over A) (SmallEtale.topology B S hS Y.1)
    (Over.equivalenceOfIsTerminal hA)
  infer_instance

/-- **Restriction to the slice at a terminal chart is an equivalence of module categories.** -/
def terminalChartOverEquivalence (hA : IsTerminal A) :
    SheafOfModules.{u} (structureRingSheaf B S hS Y) ≌
      SheafOfModules.{u} ((structureRingSheaf B S hS Y).over A) :=
  Stacks.SheafOfModules.reindexEquivalence (J := SmallEtale.topology B S hS Y.1)
    (J' := (SmallEtale.topology B S hS Y.1).over A) (Over.equivalenceOfIsTerminal hA)
    (structureRingSheaf B S hS Y)

/-- The functor of `terminalChartOverEquivalence` is restriction to the slice. -/
lemma terminalChartOverEquivalence_functor (hA : IsTerminal A) :
    (terminalChartOverEquivalence B S hS Y hA).functor =
      SheafOfModules.overFunctor (structureRingSheaf B S hS Y) A := rfl

/-- The modules on an algebraic space with a terminal étale chart `A` are the modules on the
small étale site of the scheme of `A`. -/
def terminalChartModuleEquivalence (hA : IsTerminal A) :
    SheafOfModules.{u} (structureRingSheaf B S hS Y) ≌
      SheafOfModules.{u} (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS Y A)) :=
  (terminalChartOverEquivalence B S hS Y hA).trans
    ((chartModuleReindexEquivalence B S hS Y A).trans
      (representedSmallEtaleModuleEquivalence B S hS (chartFppfObject B S hS Y A)).symm)

section Chart

variable (hA : IsTerminal A) [IsAffine (chartScheme A)]

/-- The left adjoint of the sections over a terminal affine chart, before the identification of
the ring: `M ↦ (M~)ᵃ`, the tilde of `M` on the chart's scheme made a sheaf on the small étale
site of the chart and transported to `Y`. -/
def chartTildeFunctor :
    ModuleCat.{u} Γ(chartScheme A, ⊤) ⥤ SheafOfModules.{u} (structureRingSheaf B S hS Y) :=
  (tilde.functor Γ(chartScheme A, ⊤) ⋙
      Scheme.Modules.restrictFunctor (chartScheme A).isoSpec.hom) ⋙
    _root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B) (chartScheme A)
      (chartFppfObject B S hS Y A).left.property ⋙
    (terminalChartModuleEquivalence B S hS Y hA).symm.functor

/-- The composite right adjoint of `chartTildeFunctor`. -/
def chartTopSectionsFunctor :
    SheafOfModules.{u} (structureRingSheaf B S hS Y) ⥤ ModuleCat.{u} Γ(chartScheme A, ⊤) :=
  ((terminalChartModuleEquivalence B S hS Y hA).symm.inverse ⋙
    _root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B) (chartScheme A)
      (chartFppfObject B S hS Y A).left.property) ⋙
    (Scheme.Modules.pushforward (chartScheme A).isoSpec.hom ⋙ moduleSpecΓFunctor)

/-- The adjunction `chartTildeFunctor ⊣ chartTopSectionsFunctor`. -/
def chartTildeAdjunction : chartTildeFunctor B S hS Y hA ⊣ chartTopSectionsFunctor B S hS Y hA :=
  (affineSchemeSectionsAdjunction (chartScheme A)).comp
    ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS Y A).left.property).comp
      (terminalChartModuleEquivalence B S hS Y hA).symm.toAdjunction)

/-- The unit of `chartTildeAdjunction` is invertible. -/
instance isIso_chartTildeAdjunction_unit : IsIso (chartTildeAdjunction B S hS Y hA).unit := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun M ↦ ?_
  simp only [chartTildeAdjunction, Adjunction.comp_unit_app]
  have hq : IsIso ((_root_.AlgebraicGeometry.SmallEtale.associatedModuleAdjunction
      (associatedBigEtaleSite B) (chartScheme A)
        (chartFppfObject B S hS Y A).left.property).unit.app
      ((tilde.functor Γ(chartScheme A, ⊤) ⋙
        Scheme.Modules.restrictFunctor (chartScheme A).isoSpec.hom).obj M)) :=
    _root_.AlgebraicGeometry.SmallEtale.unitIsoOnQuasicoherent (associatedBigEtaleSite B)
      (chartScheme A) (chartFppfObject B S hS Y A).left.property
      ⟨(Scheme.Modules.restrictFunctor (chartScheme A).isoSpec.hom).obj
        ((tilde.functor Γ(chartScheme A, ⊤)).obj M), inferInstance⟩
  have he : ∀ X,
      IsIso ((terminalChartModuleEquivalence B S hS Y hA).symm.toAdjunction.unit.app X) :=
    fun X ↦ by rw [Equivalence.toAdjunction_unit]; infer_instance
  have h1 : IsIso ((affineSchemeSectionsAdjunction (chartScheme A)).unit.app M) :=
    NatIso.isIso_app_of_isIso _ M
  have h2 := @IsIso.comp_isIso _ _ _ _ _ _ _ hq (@Functor.map_isIso _ _ _ _ _ _
    (_root_.AlgebraicGeometry.SmallEtale.restrictModule (associatedBigEtaleSite B) (chartScheme A)
      (chartFppfObject B S hS Y A).left.property) _ (he _))
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h1 (@Functor.map_isIso _ _ _ _ _ _ _ _ h2)

/-- The equivalence `Mod(Y) ≌ Mod(chart scheme, étale)` carries the unit module to the unit
module. -/
def terminalChartModuleEquivalenceInverseUnitIso :
    (terminalChartModuleEquivalence B S hS Y hA).inverse.obj
        (SheafOfModules.unit
          (representedSchemeStructureSheaf B S hS (chartFppfObject B S hS Y A))) ≅
      SheafOfModules.unit (structureRingSheaf B S hS Y) :=
  (terminalChartOverEquivalence B S hS Y hA).inverse.mapIso
      ((chartModuleReindexEquivalence B S hS Y A).inverse.mapIso
        (Iso.refl (SheafOfModules.unit (chartStructureRingSheaf B S hS Y A))) ≪≫
        ((chartModuleReindexEquivalence B S hS Y A).unitIso.app
          (SheafOfModules.unit ((structureRingSheaf B S hS Y).over A))).symm) ≪≫
    ((terminalChartOverEquivalence B S hS Y hA).unitIso.app
      (SheafOfModules.unit (structureRingSheaf B S hS Y))).symm

/-- `chartTildeFunctor` carries the free module of rank one to the unit module. -/
def chartTildeFunctorUnitIso :
    (chartTildeFunctor B S hS Y hA).obj (ModuleCat.of Γ(chartScheme A, ⊤) Γ(chartScheme A, ⊤)) ≅
      SheafOfModules.unit (structureRingSheaf B S hS Y) :=
  (terminalChartModuleEquivalence B S hS Y hA).inverse.mapIso
      ((_root_.AlgebraicGeometry.SmallEtale.associatedModule (associatedBigEtaleSite B)
          (chartScheme A) (chartFppfObject B S hS Y A).left.property).mapIso
          (Scheme.Modules.restrictUnitIso (chartScheme A).isoSpec.hom) ≪≫
        @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit.{u}
          (_root_.AlgebraicGeometry.SmallEtale.structureMap (associatedBigEtaleSite B)
            (chartScheme A) (chartFppfObject B S hS Y A).left.property))
          (_root_.AlgebraicGeometry.SmallEtale.isIso_pullbackObjUnitToUnit
            (associatedBigEtaleSite B) (chartScheme A)
            (chartFppfObject B S hS Y A).left.property)) ≪≫
    terminalChartModuleEquivalenceInverseUnitIso B S hS Y hA

/-- **The left adjoint `Φ` of the sections over a terminal affine chart** `A` of an algebraic
space `Y`: a module over `𝒪_Y(A)` is sent to the associated quasi-coherent `𝒪_Y`-module
(the tilde construction on the chart's affine scheme, made a sheaf on the small étale site). -/
def affineChartTilde :
    ModuleCat.{u} ((structureRingSheaf B S hS Y).obj.obj (op A)) ⥤ Modules.{u, u} B S hS Y.1 Y.2 :=
  SheafOfModules.terminalSectionsLeftAdjoint hA (chartTildeAdjunction B S hS Y hA)
    (chartTildeFunctorUnitIso B S hS Y hA)

/-- **`Φ ⊣ Γ(A, -)`** for a terminal affine chart `A`. -/
def affineChartTildeAdjunction :
    affineChartTilde B S hS Y hA ⊣
      (SheafOfModules.evaluation (structureRingSheaf B S hS Y) (op A) :
        Modules.{u, u} B S hS Y.1 Y.2 ⥤ _) :=
  SheafOfModules.terminalSectionsAdjunction hA (chartTildeAdjunction B S hS Y hA)
    (chartTildeFunctorUnitIso B S hS Y hA)

/-- The unit `M ⟶ Γ(A, Φ M)` is invertible. -/
instance isIso_affineChartTildeAdjunction_unit :
    IsIso (affineChartTildeAdjunction B S hS Y hA).unit :=
  SheafOfModules.isIso_terminalSectionsAdjunction_unit hA _ _

end Chart

end AlgebraicGeometry.Space

end

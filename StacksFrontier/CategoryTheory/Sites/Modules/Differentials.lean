module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.SmallSiteSheafification
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
import StacksCore.Tactic.StacksAttribute

/-!
# Representability of derivations of sheaves of rings

For a morphism `φ : O₁ ⟶ O₂` of sheaves of commutative rings on a site, the derivations of
`O₂` over `O₁` with values in a sheaf of `O₂`-modules form a covariant functor. This functor
is represented by a sheaf of modules, the sheaf of relative differentials.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.derivationsAddCommGrpFunctor` sends a sheaf of
  `O₂`-modules to the abelian group of its `O₁`-derivations.
* `AlgebraicGeometry.SheafOfModules.derivationsFunctor` is the underlying type-valued
  functor.
* `AlgebraicGeometry.SheafOfModules.derivationsAddCommGrpCorepresentation` upgrades a
  corepresentation of the underlying functor to a natural isomorphism of
  abelian-group-valued functors.

## Main results

* `AlgebraicGeometry.SheafOfModules.derivationsFunctor_isCorepresentable`: this functor is
  corepresentable, that is, covariantly representable.

## References

* [Stacks, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL)
-/

@[expose] public section

open CategoryTheory

universe v v₁ u u₁ w₀

namespace AlgebraicGeometry.SheafOfModules

/-- A presheaf of modules, with its sections replaced by their `ULift` to a larger universe. -/
noncomputable def liftPresheaf
    {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    (P : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat)) :
    PresheafOfModules.{max u u₁ v₁ v} (R ⋙ forget₂ CommRingCat RingCat) where
  obj X := (ModuleCat.uliftFunctor.{max u u₁ v₁ v, u} (R.obj X)).obj (P.obj X)
  map {X Y} f := (ModuleCat.uliftFunctor.{max u u₁ v₁ v, u} (R.obj X)).map (P.map f)
  map_id X := by
    ext x
    change ULift.up (P.map (𝟙 X) x.down) = _
    rw [P.map_id]
    rfl
  map_comp f g := by
    ext x
    change ULift.up (P.map (f ≫ g) x.down) = _
    rw [P.map_comp]
    rfl

/-- The universal relative derivation of presheaf differentials, lifted to a larger universe. -/
noncomputable def liftedDiffDerivation
    {C : Type u₁} [Category.{v₁} C] {S R : Cᵒᵖ ⥤ CommRingCat.{u}}
    (φ : S ⟶ R) :
    (liftPresheaf
      (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ)).Derivation' φ := by
  let P := PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ
  let d := PresheafOfModules.DifferentialsConstruction.derivation' φ
  refine PresheafOfModules.Derivation'.mk (fun X => ?_) ?_
  · exact ModuleCat.Derivation.mk (fun b => ULift.up ((d.app X).d b))
      (by intro a b; exact congrArg ULift.up ((d.app X).d_add a b))
      (by intro a b; exact congrArg ULift.up ((d.app X).d_mul a b))
      (by intro a; exact congrArg ULift.up ((d.app X).d_map a))
  · intro X Y f x
    change ULift.up (d.d (R.map f x)) = ULift.up (P.map f (d.d x))
    rw [d.d_map]
    rfl

/-- Two linear maps out of lifted Kähler differentials agree as soon as they agree on the
differentials of all sections. -/
theorem liftedDiffHom_ext
    {A B : CommRingCat.{u}} (φ : A ⟶ B) {M : Type w₀}
    [AddCommGroup M] [Module B M]
    {α β : ULift.{w₀, u} (CommRingCat.KaehlerDifferential φ) →ₗ[B] M}
    (h : ∀ b : B, α (ULift.up ((CommRingCat.KaehlerDifferential.d b))) =
      β (ULift.up (CommRingCat.KaehlerDifferential.d b))) : α = β := by
  let := φ.hom.toAlgebra
  let α' : CommRingCat.KaehlerDifferential φ →ₗ[B] M :=
    α.comp ULift.moduleEquiv.symm.toLinearMap
  let β' : CommRingCat.KaehlerDifferential φ →ₗ[B] M :=
    β.comp ULift.moduleEquiv.symm.toLinearMap
  have hspan : Submodule.span B
      (Set.range (fun b : B => CommRingCat.KaehlerDifferential.d b)) = ⊤ :=
    _root_.KaehlerDifferential.span_range_derivation (↑A) (↑B)
  have hk : LinearMap.ker (α' - β') = ⊤ := by
    rw [← top_le_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    show (α' - β') (CommRingCat.KaehlerDifferential.d b) = 0
    show α (ULift.up (CommRingCat.KaehlerDifferential.d b)) -
      β (ULift.up (CommRingCat.KaehlerDifferential.d b)) = 0
    rw [h b]
    simp
  ext x
  have h0 := congrArg (fun L : CommRingCat.KaehlerDifferential φ →ₗ[B] M => L x.down)
    (LinearMap.ker_eq_top.mp hk)
  simpa [α', β'] using (sub_eq_zero.mp h0)

/-- The lifted presheaf differentials are universal among lifted presheaves of modules. -/
noncomputable def liftedDiffUniversal
    {C : Type u₁} [Category.{v₁} C] {S R : Cᵒᵖ ⥤ CommRingCat.{u}}
    (φ : S ⟶ R) :
    PresheafOfModules.Derivation.Universal.{max u u₁ v₁ v, u, v₁, v₁, u₁, u₁}
      (liftedDiffDerivation.{v₁, u, u₁, v} φ) := by
  let P := PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ
  let Q : PresheafOfModules.{max u u₁ v₁ v} (R ⋙ forget₂ CommRingCat RingCat) :=
    liftPresheaf.{v, v₁, u, u₁} P
  let d := liftedDiffDerivation.{v₁, u, u₁, v} φ
  refine PresheafOfModules.Derivation'.Universal.mk.{max u u₁ v₁ v, u, v₁, u₁}
    (fun {M} d' => ?_) (fun {M} d' => ?_) ?_
  · refine { app := fun X => ?_, naturality := ?_ }
    · letI := (φ.app X).hom.toAlgebra
      letI : Module (R.obj X) (M.obj X) := (M.obj X).isModule
      letI : Module (S.obj X) (M.obj X) := Module.compHom (M.obj X) (φ.app X).hom
      letI : IsScalarTower (S.obj X) (R.obj X) (M.obj X) :=
        IsScalarTower.of_compHom (S.obj X) (R.obj X) (M.obj X)
      letI : Module (R.obj X) (P.obj X) := (P.obj X).isModule
      letI : Module (R.obj X) (Q.obj X) := (Q.obj X).isModule
      exact ModuleCat.ofHom (((_root_.KaehlerDifferential.linearMapEquivDerivation
        (S.obj X) (R.obj X)).symm (d'.app X)).comp
          (ULift.moduleEquiv.{u, u, max u u₁ v₁ v}
            (R := R.obj X) (M := P.obj X)).toLinearMap)
    · intro X Y f
      apply ModuleCat.hom_ext
      apply liftedDiffHom_ext (φ := φ.app X)
      intro b
      let := (φ.app X).hom.toAlgebra
      let : Module (R.obj X) (M.obj X) := (M.obj X).isModule
      let : Module (S.obj X) (M.obj X) := Module.compHom (M.obj X) (φ.app X).hom
      let : IsScalarTower (S.obj X) (R.obj X) (M.obj X) :=
        IsScalarTower.of_compHom (S.obj X) (R.obj X) (M.obj X)
      let := (φ.app Y).hom.toAlgebra
      let : Module (R.obj Y) (M.obj Y) := (M.obj Y).isModule
      let : Module (S.obj Y) (M.obj Y) := Module.compHom (M.obj Y) (φ.app Y).hom
      let : IsScalarTower (S.obj Y) (R.obj Y) (M.obj Y) :=
        IsScalarTower.of_compHom (S.obj Y) (R.obj Y) (M.obj Y)
      let eX := _root_.KaehlerDifferential.linearMapEquivDerivation
        (S.obj X) (R.obj X) (M := M.obj X)
      let eY := _root_.KaehlerDifferential.linearMapEquivDerivation
        (S.obj Y) (R.obj Y) (M := M.obj Y)
      let ηX := ((eX.symm (d'.app X)).comp
        (ULift.moduleEquiv.{u, u, max u u₁ v₁ v} (R := R.obj X)
          (M := P.obj X)).toLinearMap)
      let ηY := ((eY.symm (d'.app Y)).comp
        (ULift.moduleEquiv.{u, u, max u u₁ v₁ v} (R := R.obj Y)
          (M := P.obj Y)).toLinearMap)
      have hy : ηY (d.d (R.map f b)) = d'.d (R.map f b) :=
        congrArg (fun D : (M.obj Y).Derivation (φ.app Y) => D.d (R.map f b))
          (eY.apply_symm_apply (d'.app Y))
      have hx : ηX (d.d b) = d'.d b :=
        congrArg (fun D : (M.obj X).Derivation (φ.app X) => D.d b) (eX.apply_symm_apply (d'.app X))
      change ηY (Q.map f (d.d b)) = M.map f (ηX (d.d b))
      rw [← d.d_map, hy, d'.d_map, ← hx]
  · ext X b
    let := (φ.app X).hom.toAlgebra
    let : Module (R.obj X) (M.obj X) := (M.obj X).isModule
    let : Module (S.obj X) (M.obj X) := Module.compHom (M.obj X) (φ.app X).hom
    let : IsScalarTower (S.obj X) (R.obj X) (M.obj X) :=
      IsScalarTower.of_compHom (S.obj X) (R.obj X) (M.obj X)
    let e := _root_.KaehlerDifferential.linearMapEquivDerivation
      (S.obj X) (R.obj X) (M := M.obj X)
    exact congrArg (fun D : (M.obj X).Derivation (φ.app X) => D.d b) (e.apply_symm_apply (d'.app X))
  · intro M α β h
    apply PresheafOfModules.Hom.ext
    funext X
    apply ModuleCat.hom_ext
    apply liftedDiffHom_ext (φ := φ.app X)
    exact PresheafOfModules.Derivation.congr_d h

/-- The zero relative derivation. -/
def zeroDerivation {C : Type u₁} [Category.{v₁} C]
    {S R : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R)
    (M : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat)) :
    M.Derivation' φ where
  d := 0
  d_mul := by simp
  d_map := by
    intros X Y f x
    simp only [AddMonoidHom.zero_apply]
    exact (M.map f).hom.map_zero.symm
  d_app := by intros; rfl

/-- The pointwise sum of relative derivations. -/
def addDerivation {C : Type u₁} [Category.{v₁} C]
    {S R : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R)
    (M : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))
    (D E : M.Derivation' φ) : M.Derivation' φ where
  d := D.d + E.d
  d_mul := by
    intros
    simp only [AddMonoidHom.add_apply, D.d_mul, E.d_mul]
    module
  d_map := by
    intros
    simp only [AddMonoidHom.add_apply, D.d_map, E.d_map, map_add]
    rfl
  d_app := by
    intro X a
    simp only [AddMonoidHom.add_apply]
    exact (congrArg₂ (fun x y ↦ x + y) (D.d_app a) (E.d_app a)).trans (add_zero 0)

/-- The pointwise negative of a relative derivation. -/
def negDerivation {C : Type u₁} [Category.{v₁} C]
    {S R : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R)
    (M : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat))
    (D : M.Derivation' φ) : M.Derivation' φ where
  d := -D.d
  d_mul := by
    intros
    simp only [AddMonoidHom.neg_apply, D.d_mul]
    module
  d_map := by
    intros
    simp only [AddMonoidHom.neg_apply, D.d_map, map_neg]
    rfl
  d_app := by
    intro X a
    simp only [AddMonoidHom.neg_apply]
    exact (congrArg Neg.neg (D.d_app a)).trans neg_zero

/-- Relative derivations with values in a presheaf of modules form an additive commutative
group under pointwise addition. -/
instance derivationAddCommGroup {C : Type u₁} [Category.{v₁} C]
    {S R : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ R)
    (M : PresheafOfModules.{v} (R ⋙ forget₂ CommRingCat RingCat)) :
    AddCommGroup (M.Derivation' φ) := by
  letI : Zero (M.Derivation' φ) := ⟨zeroDerivation φ M⟩
  letI : Add (M.Derivation' φ) := ⟨addDerivation φ M⟩
  letI : Neg (M.Derivation' φ) := ⟨negDerivation φ M⟩
  exact
    { nsmul := nsmulRec
      zsmul := zsmulRec
      add_assoc D E G := by ext X x; exact add_assoc _ _ _
      zero_add D := by ext X x; exact zero_add _
      add_zero D := by ext X x; exact add_zero _
      neg_add_cancel D := by ext X x; exact neg_add_cancel _
      add_comm D E := by ext X x; exact add_comm _ _ }

/-- Derivations with values in a sheaf of modules over
`Stacks.SheafOfModules.Tensor.ringSheaf O₂` form an additive commutative group. -/
instance derivationAddCommGroupSheaf {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {O₁ O₂ : Sheaf J CommRingCat.{u}} (φ : O₁ ⟶ O₂)
    (F : _root_.SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf O₂)) :
    AddCommGroup (F.val.Derivation' φ.hom) :=
  derivationAddCommGroup (M := F.val) φ.hom

/-- The covariant functor taking an `O₂`-module sheaf to the abelian group of derivations of
`O₂` over `O₁` with values in that module. Its action on morphisms is postcomposition. -/
@[ega "0 20.2.1" "Clause 20.2.1.1"]
noncomputable def derivationsAddCommGrpFunctor {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O₁ O₂ : Sheaf J CommRingCat.{u}) (φ : O₁ ⟶ O₂) :
    _root_.SheafOfModules.{max u u₁ v₁ v} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⥤
      AddCommGrpCat.{max u u₁ v₁ v} where
  obj F := AddCommGrpCat.of (F.val.Derivation' φ.hom)
  map {X Y} f := AddCommGrpCat.ofHom
    { toFun := fun D ↦ D.postcomp f.val
      map_zero' := by ext U x; exact (f.val.app U).hom.map_zero
      map_add' := by intros; ext U x; exact (f.val.app U).hom.map_add _ _ }
  map_id F := by
    apply AddCommGrpCat.hom_ext
    ext D U x
    rfl
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    ext D U x
    rfl

/-- The underlying type-valued functor of `derivationsAddCommGrpFunctor`. -/
noncomputable abbrev derivationsFunctor {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O₁ O₂ : Sheaf J CommRingCat.{u}) (φ : O₁ ⟶ O₂) :=
  derivationsAddCommGrpFunctor.{v} O₁ O₂ φ ⋙ forget AddCommGrpCat

/-- A corepresentation of derivations as sets canonically gives a corepresentation as
abelian groups, with the same natural bijections. -/
noncomputable def derivationsAddCommGrpCorepresentation {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O₁ O₂ : Sheaf J CommRingCat.{u}) (φ : O₁ ⟶ O₂)
    {Ω : _root_.SheafOfModules.{max u u₁ v₁ v} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)}
    (e : (derivationsFunctor.{v} O₁ O₂ φ).CorepresentableBy Ω) :
    preadditiveCoyoneda.obj (Opposite.op Ω) ≅
      derivationsAddCommGrpFunctor.{v} O₁ O₂ φ := by
  refine NatIso.ofComponents (fun F ↦ AddEquiv.toAddCommGrpIso
    { toEquiv := e.homEquiv
      map_add' := ?_ }) ?_
  · intro f g
    change e.homEquiv (f + g) = e.homEquiv f + e.homEquiv g
    rw [e.homEquiv_eq (f + g), e.homEquiv_eq f, e.homEquiv_eq g]
    let D : Ω.val.Derivation' φ.hom := e.homEquiv (𝟙 Ω)
    change D.postcomp (f + g).val = D.postcomp f.val + D.postcomp g.val
    ext U x
    rfl
  · intro F G f
    exact AddCommGrpCat.ext (fun g ↦ e.homEquiv_comp f g)

universe w

/-- Sheafification of abelian presheaves exists on an essentially small site. -/
theorem siteHasSheafify {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} [EssentiallySmall.{w} C] :
    HasSheafify J AddCommGrpCat.{w} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall J

/-- On an essentially small site, sheafification inverts exactly the locally bijective maps. -/
theorem siteWEqualsLocallyBijective {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} [EssentiallySmall.{w} C] :
    J.WEqualsLocallyBijective AddCommGrpCat.{w} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v₁, _, u₁, _, w} J

/-- A derivation through which every derivation factors uniquely corepresents the derivations
functor. -/
noncomputable def universalDerivationCorepresentableBy
    {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O₁ O₂ : Sheaf J CommRingCat.{u}) (φ : O₁ ⟶ O₂)
    {Ω : _root_.SheafOfModules.{max u u₁ v₁ v} (Stacks.SheafOfModules.Tensor.ringSheaf O₂)}
    (d : Ω.val.Derivation' φ.hom)
    (h : ∀ (F : _root_.SheafOfModules.{max u u₁ v₁ v} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
      (D : F.val.Derivation' φ.hom), ∃! f : Ω ⟶ F, d.postcomp f.val = D) :
    (derivationsFunctor.{v} O₁ O₂ φ).CorepresentableBy Ω := by
  refine { homEquiv := ?_, homEquiv_comp := ?_ }
  · intro F
    refine ⟨fun f ↦ d.postcomp f.val, fun D ↦ Classical.choose (h F D), ?_, ?_⟩
    · intro f
      exact ((Classical.choose_spec (h F (d.postcomp f.val))).2 f rfl).symm
    · intro D
      exact (Classical.choose_spec (h F D)).1
  · intro F G g f
    change d.postcomp (f.val ≫ g.val) = (d.postcomp f.val).postcomp g.val
    ext X x
    rfl

/-- For a homomorphism of sheaves of commutative rings, the functor
sending a sheaf of modules to the type of relative derivations is represented by a sheaf
of modules. -/
@[stacks 04BL]
instance derivationsFunctor_isCorepresentable {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    (O₁ O₂ : Sheaf J CommRingCat.{u}) (φ : O₁ ⟶ O₂) :
    (derivationsFunctor.{v} O₁ O₂ φ).IsCorepresentable := by
  let : EssentiallySmall.{max u u₁ v₁ v} C := inferInstance
  let : HasSheafify J AddCommGrpCat.{max u u₁ v₁ v} := siteHasSheafify (J := J)
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max u u₁ v₁ v} :=
    siteWEqualsLocallyBijective (J := J)
  let Q : PresheafOfModules.{max u u₁ v₁ v} (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj :=
    liftPresheaf.{v, v₁, u, u₁}
      (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)
  let S : _root_.SheafOfModules.{max u u₁ v₁ v} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) :=
    (PresheafOfModules.sheafification.{max u u₁ v₁ v}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).obj Q
  let η :=
    (PresheafOfModules.sheafificationAdjunction
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app Q
  let d : Q.Derivation' φ.hom := liftedDiffDerivation.{v₁, u, u₁, v} φ.hom
  let dS : ((_root_.SheafOfModules.forget
      (Stacks.SheafOfModules.Tensor.ringSheaf O₂)).obj S).Derivation' φ.hom :=
    d.postcomp η
  have hUniversal :
      ∀ (F : _root_.SheafOfModules.{max u u₁ v₁ v} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
        (D : F.val.Derivation' φ.hom), ∃! f : S ⟶ F, dS.postcomp f.val = D := by
    intro F D
    let eQ := liftedDiffUniversal.{max u u₁ v₁ v, v₁, u, u₁} φ.hom
    let g := eQ.desc D
    let f := (PresheafOfModules.sheafificationHomEquiv
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).symm g
    have hmap : η ≫ f.val = g := by
      change PresheafOfModules.sheafificationHomEquiv
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj) f = g
      exact Equiv.apply_symm_apply _ g
    refine ⟨f, ?_, ?_⟩
    · change dS.postcomp f.val = D
      exact (show dS.postcomp f.val = d.postcomp (η ≫ f.val) by ext X x; rfl).trans
        ((congrArg (fun k : Q ⟶ F.val => d.postcomp k) hmap).trans (eQ.fac D))
    · intro f' hf'
      have hf : d.postcomp (η ≫ f'.val) = D :=
        (show d.postcomp (η ≫ f'.val) = dS.postcomp f'.val by ext X x; rfl).trans hf'
      apply (PresheafOfModules.sheafificationHomEquiv
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₂)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).injective
      change η ≫ f'.val = η ≫ f.val
      exact (hmap.trans
        (eQ.postcomp_injective g (η ≫ f'.val) (by rw [eQ.fac D]; exact hf.symm))).symm
  exact (universalDerivationCorepresentableBy O₁ O₂ φ dS hUniversal).isCorepresentable

end AlgebraicGeometry.SheafOfModules

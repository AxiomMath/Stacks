module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.MilnorPatching.ModuleCategory
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Descent
public import StacksFrontier.RingTheory.Flat.FaithfullyFlat.Projective
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingEquivalence
public import StacksFrontier.RingTheory.AdicCompletion.QuotientBijective
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingModuleProperties.AdicCompletion

/-!
# Tensor products of module glueing data

## Main definitions

* `FormalGlueing.LargeModuleMonoidalStructure`: the usual tensor product on a module category
  whose objects may live in a larger universe than its ring.
* `FormalGlueing.genericProjection`, `FormalGlueing.localProjection`: the component functors from
  the category of glueing data.

## Implementation notes

Mathlib currently installs the tensor-product monoidal structure on `ModuleCat.{u} R` only when
`R : Type u`. `LargeModuleMonoidalStructure` states the same structure, together with its
identification with the ordinary module tensor product, without imposing this artificial
universe equality. Its symmetry is identified with the usual flip of tensor factors.
-/

/-! ### Properties and tensor products under formal glueing -/

@[expose] public section

namespace FormalGlueing

universe u v w

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open FormalGlueing

/-- The usual symmetric tensor-product monoidal structure on modules, allowing the modules to
live in a larger universe than the coefficient ring. The displayed isomorphisms specify its
tensor and unit objects; the symmetry agrees with the ordinary tensor flip. The category fields
supply all naturality and coherence laws. -/
public structure LargeModuleMonoidalStructure (A : Type u) [CommRing A] where
  /-- The monoidal category structure on `ModuleCat A`. -/
  monoidal : MonoidalCategory (ModuleCat.{max u w} A)
  /-- The symmetric structure compatible with `monoidal`. -/
  symmetric : letI := monoidal; SymmetricCategory (ModuleCat.{max u w} A)
  /-- The tensor product object `M ⊗ N` is isomorphic to the module `M ⊗[A] N`. -/
  tensorObjIso : letI := monoidal;
    ∀ M N : ModuleCat.{max u w} A, M ⊗ N ≅ ModuleCat.of A (TensorProduct A M N)
  /-- Under `tensorObjIso`, the tensor product of morphisms is `TensorProduct.map`. -/
  tensorHomIso_naturality : letI := monoidal;
    ∀ {M M' N N' : ModuleCat.{max u w} A} (g : M ⟶ M') (h : N ⟶ N'),
      (g ⊗ₘ h) ≫ (tensorObjIso M' N').hom =
        (tensorObjIso M N).hom ≫ ModuleCat.ofHom (TensorProduct.map g.hom h.hom)
  /-- Under `tensorObjIso`, the braiding is `TensorProduct.comm`. -/
  braiding_tensorObjIso : letI := monoidal; letI := symmetric;
    ∀ M N : ModuleCat.{max u w} A,
      (β_ M N).hom ≫ (tensorObjIso N M).hom =
        (tensorObjIso M N).hom ≫ ModuleCat.ofHom (TensorProduct.comm A M N).toLinearMap
  /-- The tensor unit is isomorphic to `A`, lifted to the universe `max u w`. -/
  tensorUnitIso : letI := monoidal;
    𝟙_ (ModuleCat.{max u w} A) ≅ ModuleCat.of A (ULift.{w, u} A)

/-- Projection of a module glueing datum to its generic module. -/
public noncomputable def genericProjection
    {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (c : ModuleGlueingConstruction.{u, v, w} S f) :
    letI := c.category
    ModuleGlueingDatum.{u, v, w} S f c.comparison ⥤ ModuleCat.{max u v w} S := by
  letI := c.category
  exact
    { obj := fun X ↦ X.generic
      map := fun g ↦ (c.homEquiv _ _ g).generic
      map_id := fun X ↦ c.homEquiv_id_generic X
      map_comp := fun g h ↦ c.homEquiv_comp_generic g h }

/-- Projection of a module glueing datum to one of its local modules. -/
public noncomputable def localProjection
    {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (c : ModuleGlueingConstruction.{u, v, w} S f) (i : Fin r) :
    letI := c.category
    ModuleGlueingDatum.{u, v, w} S f c.comparison ⥤
      ModuleCat.{max u v w} (Localization.Away (f i)) := by
  letI := c.category
  exact
    { obj := fun X ↦ X.localPiece i
      map := fun g ↦ (c.homEquiv _ _ g).localPiece i
      map_id := fun X ↦ c.homEquiv_id_local X i
      map_comp := fun g h ↦ c.homEquiv_comp_local g h i }

open scoped TensorProduct
open TensorProduct

@[instance_reducible]
private noncomputable def moduleMonoidalStruct (R : Type u) [CommRing R] :
    MonoidalCategoryStruct (ModuleCat.{max u w} R) where
  tensorObj M N := ModuleCat.of R (TensorProduct R M N)
  tensorHom f g := ModuleCat.ofHom (TensorProduct.map f.hom g.hom)
  whiskerLeft M _ _ f := ModuleCat.ofHom (f.hom.lTensor M)
  whiskerRight f N := ModuleCat.ofHom (f.hom.rTensor N)
  tensorUnit := ModuleCat.of R (ULift.{w} R)
  associator M N K := (TensorProduct.assoc R M N K).toModuleIso
  leftUnitor M := ((TensorProduct.congr (ULift.moduleEquiv : ULift.{w} R ≃ₗ[R] R)
    (LinearEquiv.refl R M)).trans (TensorProduct.lid R M)).toModuleIso
  rightUnitor M := ((TensorProduct.congr (LinearEquiv.refl R M)
    (ULift.moduleEquiv : ULift.{w} R ≃ₗ[R] R)).trans (TensorProduct.rid R M)).toModuleIso

@[instance_reducible]
private noncomputable def moduleMonoidal (R : Type u) [CommRing R] :
    MonoidalCategory (ModuleCat.{max u w} R) := by
  letI := moduleMonoidalStruct.{u, w} R
  exact MonoidalCategory.ofTensorHom
    (id_tensorHom_id := fun M N ↦ by
      apply ModuleCat.hom_ext
      exact TensorProduct.ext rfl)
    (tensorHom_comp_tensorHom := fun f g h k ↦ by
      apply ModuleCat.hom_ext
      exact TensorProduct.ext rfl)
    (associator_naturality := fun f g h ↦ by
      apply ModuleCat.hom_ext
      exact TensorProduct.ext_threefold fun _ _ _ ↦ rfl)
    (leftUnitor_naturality := fun f ↦ by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro r m
      exact (f.hom.map_smul r.down m).symm)
    (rightUnitor_naturality := fun f ↦ by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro m r
      exact (f.hom.map_smul r.down m).symm)
    (pentagon := fun M N K L ↦ by
      apply ModuleCat.hom_ext
      exact TensorProduct.ext_fourfold fun _ _ _ _ ↦ rfl)
    (triangle := fun M N ↦ by
      apply ModuleCat.hom_ext
      apply TensorProduct.ext_threefold
      intro m r n
      change m ⊗ₜ[R] (r.down • n) = (r.down • m) ⊗ₜ[R] n
      exact TensorProduct.tmul_smul r.down m n)

@[instance_reducible]
private noncomputable def moduleSymmetric (R : Type u) [CommRing R] :
    letI := moduleMonoidal.{u, w} R
    SymmetricCategory (ModuleCat.{max u w} R) := by
  letI := moduleMonoidal.{u, w} R
  exact
    { braiding := fun M N ↦ (TensorProduct.comm R M N).toModuleIso
      braiding_naturality_left := fun f N ↦ by
        apply ModuleCat.hom_ext
        exact TensorProduct.ext' fun _ _ ↦ rfl
      braiding_naturality_right := fun M {N K} f ↦ by
        apply ModuleCat.hom_ext
        exact TensorProduct.ext' fun _ _ ↦ rfl
      hexagon_forward := fun M N K ↦ by
        apply ModuleCat.hom_ext
        exact TensorProduct.ext_threefold fun _ _ _ ↦ rfl
      hexagon_reverse := fun M N K ↦ by
        apply (cancel_epi (α_ M N K).hom).mp
        apply ModuleCat.hom_ext
        exact TensorProduct.ext_threefold fun _ _ _ ↦ rfl
      symmetry := fun M N ↦ by
        apply ModuleCat.hom_ext
        exact TensorProduct.ext' fun _ _ ↦ rfl }

private noncomputable def largeModuleTensor (R : Type u) [CommRing R] :
    LargeModuleMonoidalStructure.{u, w} R where
  monoidal := moduleMonoidal R
  symmetric := moduleSymmetric R
  tensorObjIso _ _ := Iso.refl _
  tensorHomIso_naturality _ _ := rfl
  braiding_tensorObjIso _ _ := rfl
  tensorUnitIso := Iso.refl _

section Transport

universe u₁ u₂ u₃ v₁ v₂ v₃
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [SymmetricCategory C]
variable {D : Type u₂} [Category.{v₂} D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [SymmetricCategory E]
@[instance_reducible]
private noncomputable def braidedOfNatIso {F G : C ⥤ E} (i : F ≅ G) [F.Braided] :
    G.Braided := by
  letI : G.Monoidal := Functor.Monoidal.transport i
  letI : i.hom.IsMonoidal := Functor.Monoidal.natTransIsMonoidal_of_transport i
  exact { __ := (inferInstance : G.Monoidal), __ := Functor.LaxBraided.ofNatIso i }
private theorem exists_braided_transport (e : C ≌ D) :
    letI := Monoidal.transport e
    ∃ (_ : SymmetricCategory D) (_ : e.functor.Braided) (_ : e.inverse.Braided),
      e.IsMonoidal := by
  let := Monoidal.transport e
  let : SymmetricCategory D := Monoidal.Transported.instSymmetricCategory e
  let : e.functor.Braided := Monoidal.instBraidedTransportedFunctorEquivalenceTransported e
  let : e.inverse.Braided := Monoidal.instBraidedTransportedInverseEquivalenceTransported e
  refine ⟨inferInstance, inferInstance, inferInstance, ?_⟩
  let : (Monoidal.equivalenceTransported e).symm.IsMonoidal := inferInstance
  exact Equivalence.isMonoidal_symm (e := (Monoidal.equivalenceTransported e).symm)
@[instance_reducible]
private noncomputable def braidedProjection (e : C ≌ D) (P : D ⥤ E) [(e.functor ⋙ P).Braided] :
    letI := Monoidal.transport e
    letI : SymmetricCategory D := Monoidal.Transported.instSymmetricCategory e
    P.Braided := by
  letI := Monoidal.transport e
  letI : SymmetricCategory D := Monoidal.Transported.instSymmetricCategory e
  letI : e.inverse.Braided := Monoidal.instBraidedTransportedInverseEquivalenceTransported e
  exact braidedOfNatIso ((Functor.associator e.inverse e.functor P).symm ≪≫
    Functor.isoWhiskerRight e.counitIso P ≪≫ Functor.leftUnitor P)

end Transport

private theorem moduleProperties_iff_faithfullyFlat_baseChange
    (R : Type u) (S : Type v) (M : Type w) [CommRing R] [CommRing S]
    [Algebra R S] [AddCommGroup M] [Module R M] [Module.FaithfullyFlat R S] :
    (Module.Finite R M ↔ Module.Finite S (S ⊗[R] M)) ∧
    (Module.FinitePresentation R M ↔ Module.FinitePresentation S (S ⊗[R] M)) ∧
    (Module.Flat R M ↔ Module.Flat S (S ⊗[R] M)) ∧
    (Module.Projective R M ↔ Module.Projective S (S ⊗[R] M)) := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro h; let := h; infer_instance
  · intro h; let := h
    exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S
  · intro h; let := h; infer_instance
  · intro h; let := h
    exact Module.FinitePresentation.of_isBaseChange_of_faithfullyFlat
      ((TensorProduct.mk R S M) 1) (TensorProduct.isBaseChange (R := R) (S := S) (M := M))
  · intro h; let := h; infer_instance
  · intro h; let := h
    exact Module.Flat.of_flat_tensorProduct R M S
  · intro h; let := h; infer_instance
  · intro h; let := h
    exact Module.Projective.of_projective_tensorProduct S

set_option maxHeartbeats 2000000 in
-- Tensor coherence involves several nested scalar extensions and their module structures.
set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private noncomputable def scalarExtensionMonoidal
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    letI := moduleMonoidal.{u, max v w} R
    letI := moduleMonoidal.{v, max u w} S
    (ModuleCat.extendScalars.{u, v, max u v w} f).Monoidal := by
  letI := moduleMonoidal.{u, max v w} R
  letI := moduleMonoidal.{v, max u w} S
  letI := f.toAlgebra
  let unit : TensorProduct R S (ULift.{max v w} R) ≃ₗ[S] ULift.{max u w} S :=
    (AlgebraTensorModule.congr (LinearEquiv.refl S S) ULift.moduleEquiv).trans
      ((AlgebraTensorModule.rid R S S).trans ULift.moduleEquiv.symm)
  exact Functor.CoreMonoidal.toMonoidal
    (Functor.CoreMonoidal.mk'
      (εIso := unit.symm.toModuleIso)
      (μIso := fun M N ↦ (AlgebraTensorModule.distribBaseChange R S M N).symm.toModuleIso)
      (μIso_inv_natural_left := fun {M M'} g N ↦ by
        apply ModuleCat.ExtendScalars.hom_ext
        intro t
        change TensorProduct.map (g.hom.baseChange S) LinearMap.id
            (AlgebraTensorModule.distribBaseChange R S M N ((1 : S) ⊗ₜ[R] t)) =
          AlgebraTensorModule.distribBaseChange R S M' N
            ((1 : S) ⊗ₜ[R] TensorProduct.map g.hom LinearMap.id t)
        induction t using TensorProduct.inductionOn with
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
        | tmul m n => rfl)
      (μIso_inv_natural_right := fun {N N'} M g ↦ by
        apply ModuleCat.ExtendScalars.hom_ext
        intro t
        change TensorProduct.map LinearMap.id (g.hom.baseChange S)
            (AlgebraTensorModule.distribBaseChange R S M N ((1 : S) ⊗ₜ[R] t)) =
          AlgebraTensorModule.distribBaseChange R S M N'
            ((1 : S) ⊗ₜ[R] TensorProduct.map LinearMap.id g.hom t)
        induction t using TensorProduct.inductionOn with
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
        | tmul m n => rfl)
      (oplax_associativity := fun M N K ↦ by
        apply ModuleCat.ExtendScalars.hom_ext
        intro t
        change TensorProduct.assoc S (S ⊗[R] M) (S ⊗[R] N) (S ⊗[R] K)
            (TensorProduct.map (AlgebraTensorModule.distribBaseChange R S M N).toLinearMap
              LinearMap.id (AlgebraTensorModule.distribBaseChange R S (M ⊗[R] N) K
                ((1 : S) ⊗ₜ[R] t))) =
          TensorProduct.map LinearMap.id (AlgebraTensorModule.distribBaseChange R S N K).toLinearMap
            (AlgebraTensorModule.distribBaseChange R S M (N ⊗[R] K)
              ((1 : S) ⊗ₜ[R] TensorProduct.assoc R M N K t))
        induction t using TensorProduct.inductionOn with
        | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
        | tmul x k =>
          induction x using TensorProduct.inductionOn with
          | add x y hx hy => simp only [TensorProduct.add_tmul, TensorProduct.tmul_add, map_add, hx,
            hy]
          | tmul m n => rfl)
      (oplax_left_unitality := fun M ↦ by
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        change (ULift.up (1 : S)) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m) =
          (unit ((1 : S) ⊗ₜ[R] (ULift.up (1 : R)))) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)
        congr 1
        change ULift.up (1 : S) = ULift.up ((1 : R) • (1 : S))
        rw [one_smul])
      (oplax_right_unitality := fun M ↦ by
        apply ModuleCat.ExtendScalars.hom_ext
        intro m
        change ((1 : S) ⊗ₜ[R] m) ⊗ₜ[S] (ULift.up (1 : S)) =
          ((1 : S) ⊗ₜ[R] m) ⊗ₜ[S] (unit ((1 : S) ⊗ₜ[R] (ULift.up (1 : R))))
        congr 1
        change ULift.up (1 : S) = ULift.up ((1 : R) • (1 : S))
        rw [one_smul]))

-- Normalize the two tensor flips through extension of scalars.
set_option backward.isDefEq.respectTransparency false in
@[instance_reducible]
private noncomputable def scalarExtensionBraided
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    letI := moduleMonoidal.{u, max v w} R
    letI := moduleMonoidal.{v, max u w} S
    letI := moduleSymmetric.{u, max v w} R
    letI := moduleSymmetric.{v, max u w} S
    (ModuleCat.extendScalars.{u, v, max u v w} f).Braided := by
  letI := moduleMonoidal.{u, max v w} R
  letI := moduleMonoidal.{v, max u w} S
  letI := moduleSymmetric.{u, max v w} R
  letI := moduleSymmetric.{v, max u w} S
  letI := f.toAlgebra
  refine { __ := scalarExtensionMonoidal f, braided := ?_ }
  intro M N
  apply ModuleCat.hom_ext
  change ((TensorProduct.comm R M N).toLinearMap.baseChange S).comp
      (AlgebraTensorModule.distribBaseChange R S M N).symm.toLinearMap =
    (AlgebraTensorModule.distribBaseChange R S N M).symm.toLinearMap.comp
      (TensorProduct.comm S (S ⊗[R] M) (S ⊗[R] N)).toLinearMap
  apply TensorProduct.ext'
  intro x y
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => simp only [TensorProduct.add_tmul, map_add, hx, hx']
  | tmul a m =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => simp only [TensorProduct.tmul_add, map_add, hy, hy']
    | tmul b n =>
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe,
        AlgebraTensorModule.distribBaseChange_symm_tmul, LinearMap.baseChange_tmul,
        TensorProduct.comm_tmul, mul_comm]

private noncomputable def largeExtendScalarsEquiv
    {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (M : ModuleCat.{max u v w} R) :
    (ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S)).obj M ≃ₗ[S]
      S ⊗[R] M := by
  let SR := (ModuleCat.restrictScalars (algebraMap R S)).obj (ModuleCat.of S S)
  letI : Module S SR := inferInstanceAs (Module S S)
  letI : IsScalarTower R S SR := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact AlgebraTensorModule.congr (show SR ≃ₗ[S] S from LinearEquiv.refl S S)
    (LinearEquiv.refl R M)

set_option backward.isDefEq.respectTransparency false in
private noncomputable def canonicalGenericIso
    {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) :
    let c := moduleGlueingConstruction.{u, v, w} S f
    letI := c.category
    c.canonical ⋙ genericProjection S f c ≅
      ModuleCat.extendScalars.{u, v, max u v w} (algebraMap R S) := by
  exact NatIso.ofComponents (fun M ↦ (largeExtendScalarsEquiv S M).symm.toModuleIso)
    (fun g ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro t
      induction t using TensorProduct.inductionOn with
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul s m => rfl)


set_option backward.isDefEq.respectTransparency false in
private noncomputable def canonicalLocalIso
    {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (i : Fin r) :
    let c := moduleGlueingConstruction.{u, v, w} S f
    letI := c.category
    c.canonical ⋙ localProjection S f c i ≅
      ModuleCat.extendScalars.{u, u, max u v w}
        (algebraMap R (Localization.Away (f i))) := by
  let c := moduleGlueingConstruction.{u, v, w} S f
  letI := c.category
  let A := Localization.Away (f i)
  let e (M : ModuleCat.{max u v w} R) :=
    ((c.canonicalLocal M i).trans
      (LocalizedModule.equivTensorProduct (Submonoid.powers (f i)) M)).trans
        (largeExtendScalarsEquiv.{u, u, max u v w} A M).symm
  refine (NatIso.ofComponents (fun M ↦ (e M).symm.toModuleIso) ?_).symm
  intro M N g
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change (e N).symm ((1 : A) ⊗ₜ[R] g m) =
    (c.homEquiv _ _ (c.canonical.map g)).localPiece i
      ((e M).symm ((1 : A) ⊗ₜ[R] m))
  apply (c.canonicalLocal N i).injective
  change (c.canonicalLocal N i) ((c.canonicalLocal N i).symm
      ((LocalizedModule.equivTensorProduct (Submonoid.powers (f i)) N).symm
        ((1 : A) ⊗ₜ[R] g m))) =
    (c.canonicalLocal N i)
      ((c.homEquiv _ _ (c.canonical.map g)).localPiece i
        ((c.canonicalLocal M i).symm
          ((LocalizedModule.equivTensorProduct (Submonoid.powers (f i)) M).symm
            ((1 : A) ⊗ₜ[R] m))))
  simp only [LinearEquiv.apply_symm_apply,
    LocalizedModule.equivTensorProduct_symm_apply_tmul_one]
  exact (c.canonicalMapLocal g i m).symm

private abbrev moduleProperty (k : Fin 4) (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] : Prop :=
  ![Module.Finite R M, Module.FinitePresentation R M, Module.Flat R M,
    Module.Projective R M] k

private theorem moduleProperty_equiv_iff (k : Fin 4) {R M N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] (e : M ≃ₗ[R] N) :
    moduleProperty k R M ↔ moduleProperty k R N := by
  fin_cases k
  · exact Module.Finite.equiv_iff e
  · exact e.finitePresentation_iff
  · exact Module.Flat.equiv_iff e
  · exact ⟨fun h ↦ @Module.Projective.of_equiv' _ _ _ _ _ _ _ _ h e,
      fun h ↦ @Module.Projective.of_equiv' _ _ _ _ _ _ _ _ h e.symm⟩

private theorem moduleProperty_baseChange (k : Fin 4) (R S M : Type*)
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
    (h : moduleProperty k R M) : moduleProperty k S (S ⊗[R] M) := by
  fin_cases k <;> dsimp [moduleProperty] at h ⊢ <;> let := h <;> infer_instance

private theorem moduleProperty_restrictScalars (k : Fin 4) (R S M : Type*)
    [CommRing R] [CommRing S] [Algebra R S] [AddCommGroup M] [Module R M]
    [Module S M] [IsScalarTower R S M] [Module.Finite R S] [Module.Projective R S]
    (h : moduleProperty k S M) : moduleProperty k R M := by
  fin_cases k <;> dsimp [moduleProperty] at h ⊢
  · let := h; exact Module.Finite.trans S M
  · let := h
    have : Module.FinitePresentation R S := Module.finitePresentation_of_projective R S
    exact Module.FinitePresentation.trans R M S
  · let := h; exact Module.Flat.trans R S M
  · classical
    let := h
    have : Module.Projective R (M →₀ S) :=
      Module.Projective.of_equiv' (finsuppLequivDFinsupp R).symm
    obtain ⟨i, hi⟩ := (Module.projective_def' (R := S) (P := M)).mp h
    exact Module.Projective.of_split (i.restrictScalars R)
      ((Finsupp.linearCombination S id).restrictScalars R)
      (congrArg (LinearMap.restrictScalars R) hi)

private theorem moduleProperty_prod (k : Fin 4) (R M N : Type*)
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (hM : moduleProperty k R M) (hN : moduleProperty k R N) :
    moduleProperty k R (M × N) := by
  fin_cases k <;> dsimp [moduleProperty] at hM hN ⊢ <;> let := hM <;> let := hN
  · infer_instance
  · infer_instance
  · rw [Module.Flat.iff_rTensor_injectiveₛ]
    intro P _ _ Q
    have h : (TensorProduct.prodRight R R P M N).toLinearMap.comp
        (Q.subtype.rTensor (M × N)) =
        (LinearMap.prodMap (Q.subtype.rTensor M) (Q.subtype.rTensor N)).comp
          (TensorProduct.prodRight R R Q M N).toLinearMap := by
      ext x y <;> rfl
    have hi := (Module.Flat.rTensor_preserves_injective_linearMap (M := M)
      Q.subtype Q.subtype_injective).prodMap
      (Module.Flat.rTensor_preserves_injective_linearMap (M := N)
        Q.subtype Q.subtype_injective)
    exact Function.Injective.of_comp (g := (Q.subtype.rTensor (M × N)))
      (f := TensorProduct.prodRight R R P M N)
      (by rw [← LinearEquiv.coe_coe, ← LinearMap.coe_comp, h]
          exact hi.comp (TensorProduct.prodRight R R Q M N).injective)
  · infer_instance

private theorem moduleProperty_pi (k : Fin 4) (R : Type*) {ι : Type*} [Finite ι]
    (M : ι → Type*) [CommRing R] [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    (hM : ∀ i, moduleProperty k R (M i)) : moduleProperty k R (∀ i, M i) := by
  classical
  let := Fintype.ofFinite ι
  fin_cases k <;> dsimp [moduleProperty] at hM ⊢ <;> let := hM
  · infer_instance
  · infer_instance
  · exact Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := R)).symm
  · exact Module.Projective.of_equiv' (DFinsupp.linearEquivFunOnFintype (R := R))

private theorem finite_projective_of_retract (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] (i : S →ₗ[R] R) (hi : (Algebra.linearMap R S).comp i = LinearMap.id) :
    Module.Finite R S ∧ Module.Projective R S := by
  have hs : Function.Surjective (Algebra.linearMap R S) :=
    Function.HasRightInverse.surjective ⟨i, fun x ↦ LinearMap.congr_fun hi x⟩
  exact ⟨Module.Finite.of_surjective (Algebra.linearMap R S) hs,
    Module.Projective.of_split i (Algebra.linearMap R S) hi⟩

private theorem moduleProperty_piRing (k : Fin 4) {ι : Type*} [Finite ι]
    (S : ι → Type*) [∀ i, CommRing (S i)] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module (S i) (M i)]
    (hM : ∀ i, moduleProperty k (S i) (M i)) :
    moduleProperty k (∀ i, S i) (∀ i, M i) := by
  classical
  let P := ∀ i, S i
  let (i : ι) : Algebra P (S i) := (Pi.evalRingHom S i).toAlgebra
  let (i : ι) : Module P (M i) := Module.compHom (M i) (Pi.evalRingHom S i)
  let (i : ι) : IsScalarTower P (S i) (M i) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hp (i : ι) : Module.Finite P (S i) ∧ Module.Projective P (S i) := by
    let l : S i →ₗ[P] P :=
      { toFun := Pi.single i
        map_add' := fun x y ↦ Pi.single_add i x y
        map_smul' := fun x y ↦ by
          ext j
          change Pi.single i (x i * y) j = x j * Pi.single i y j
          by_cases h : j = i
          · subst j; simp
          · simp [h] }
    exact finite_projective_of_retract P (S i) l (by ext x; change Pi.single i x i = x; simp)
  apply moduleProperty_pi k P M
  intro i
  have := (hp i).1
  have := (hp i).2
  exact moduleProperty_restrictScalars k P (S i) (M i) (hM i)

private theorem moduleProperty_prodRing (k : Fin 4) (S T M N : Type*)
    [CommRing S] [CommRing T] [AddCommGroup M] [AddCommGroup N]
    [Module S M] [Module T N]
    (hM : moduleProperty k S M) (hN : moduleProperty k T N) :
    letI : Module (S × T) M := Module.compHom M (RingHom.fst S T)
    letI : Module (S × T) N := Module.compHom N (RingHom.snd S T)
    moduleProperty k (S × T) (M × N) := by
  let : Algebra (S × T) S := (RingHom.fst S T).toAlgebra
  let : Algebra (S × T) T := (RingHom.snd S T).toAlgebra
  let : Module (S × T) M := Module.compHom M (RingHom.fst S T)
  let : Module (S × T) N := Module.compHom N (RingHom.snd S T)
  let : IsScalarTower (S × T) S M := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : IsScalarTower (S × T) T N := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hs := finite_projective_of_retract (S × T) S
    (LinearMap.inl (S × T) S T) (by ext; rfl)
  have ht := finite_projective_of_retract (S × T) T
    (LinearMap.inr (S × T) S T) (by ext; rfl)
  have := hs.1
  have := hs.2
  have := ht.1
  have := ht.2
  exact moduleProperty_prod k (S × T) M N
    (moduleProperty_restrictScalars k (S × T) S M hM)
    (moduleProperty_restrictScalars k (S × T) T N hN)


set_option backward.isDefEq.respectTransparency false in
private theorem eq_zero_of_glueing_baseChange
    {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range f)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (M : ModuleCat.{max u v w} R) (m : M)
    (hs : (1 : S) ⊗ₜ[R] m = 0)
    (hl : ∀ i, (1 : Localization.Away (f i)) ⊗ₜ[R] m = 0) : m = 0 := by
  let c := moduleGlueingConstruction.{u, v, w} S f
  let := c.category
  have : IsIso c.canonicalSectionsUnit := FormalGlueing.canonicalSectionsUnit_isIso R S f hflat hq
  apply ((asIso c.canonicalSectionsUnit).app M).toLinearEquiv.injective
  rw [map_zero]
  apply (c.sectionsObj (c.canonical.obj M)).injective
  apply Subtype.ext
  apply Prod.ext
  · apply (c.canonicalGeneric M).injective
    change (c.canonicalGeneric M)
      ((c.sectionsObj (c.canonical.obj M) (c.canonicalSectionsUnit.app M m)).1.1) =
        (c.canonicalGeneric M) 0
    rw [map_zero]
    exact (c.canonicalSectionsUnit_generic M m).trans hs
  · funext i
    apply (c.canonicalLocal M i).injective
    change (c.canonicalLocal M i)
      ((c.sectionsObj (c.canonical.obj M) (c.canonicalSectionsUnit.app M m)).1.2 i) =
        (c.canonicalLocal M i) 0
    rw [map_zero, c.canonicalSectionsUnit_local]
    simpa only [LocalizedModule.equivTensorProduct_symm_apply_tmul_one,
      LocalizedModule.mkLinearMap_apply, map_zero] using
      congrArg (LocalizedModule.equivTensorProduct (Submonoid.powers (f i)) M).symm (hl i)

private theorem faithfullyFlat_glueingProduct
    {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range f)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map)) :
    Module.FaithfullyFlat R (S × ∀ i, Localization.Away (f i)) := by
  let T := ∀ i, Localization.Away (f i)
  let P := S × T
  rw [Module.FaithfullyFlat.iff_flat_and_lTensor_reflects_triviality]
  refine ⟨moduleProperty_prod 2 R S T hflat
    (moduleProperty_pi 2 R _ fun i ↦
      inferInstanceAs (Module.Flat R (Localization.Away (f i)))), ?_⟩
  intro M _ _ hM
  let := hM
  apply subsingleton_of_forall_eq 0
  intro m
  apply eq_zero_of_glueing_baseChange.{u, v, 0} S f hflat hq (ModuleCat.of R M) m
  · simpa only [TensorProduct.map_tmul, LinearMap.fst_apply, LinearMap.id_apply,
      Prod.fst_one, map_zero] using congrArg (TensorProduct.map (LinearMap.fst R S T) LinearMap.id)
        (Subsingleton.elim ((1 : P) ⊗ₜ[R] m) 0)
  · intro i
    have h := congrArg (TensorProduct.map
      ((LinearMap.proj i).comp (LinearMap.snd R S T)) LinearMap.id)
      (Subsingleton.elim ((1 : P) ⊗ₜ[R] m) 0)
    simpa only [TensorProduct.map_tmul, LinearMap.comp_apply, LinearMap.snd_apply,
      LinearMap.proj_apply, LinearMap.id_apply, Prod.snd_one, Pi.one_apply, map_zero, T] using h

private noncomputable def tensorPiLeft
    (R : Type*) {ι : Type*} [Fintype ι] (S : ι → Type*)
    [CommRing R] [∀ i, CommRing (S i)] [∀ i, Algebra R (S i)]
    (M : Type*) [AddCommGroup M] [Module R M] :
    ((∀ i, S i) ⊗[R] M) ≃ₗ[∀ i, S i] ∀ i, S i ⊗[R] M := by
  classical
  let e : ((∀ i, S i) ⊗[R] M) ≃ₗ[R] ∀ i, S i ⊗[R] M :=
    (TensorProduct.comm R _ _).trans ((TensorProduct.piRight R R M S).trans
      (LinearEquiv.piCongrRight fun i ↦ TensorProduct.comm R M (S i)))
  refine e.toAddEquiv.toLinearEquiv ?_
  intro s x
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  | tmul a m =>
    ext i
    simp [e, TensorProduct.smul_tmul']

private theorem moduleProperty_baseChange_prod (k : Fin 4) (R S T M : Type*)
    [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
    [AddCommGroup M] [Module R M]
    (hs : moduleProperty k S (S ⊗[R] M)) (ht : moduleProperty k T (T ⊗[R] M)) :
    moduleProperty k (S × T) ((S × T) ⊗[R] M) := by
  let : Algebra (S × T) S := (RingHom.fst S T).toAlgebra
  let : Algebra (S × T) T := (RingHom.snd S T).toAlgebra
  let : IsScalarTower R (S × T) S := IsScalarTower.of_algebraMap_smul fun r s ↦ by
    change algebraMap R S r * s = r • s
    exact (Algebra.smul_def r s).symm
  let : IsScalarTower R (S × T) T := IsScalarTower.of_algebraMap_smul fun r t ↦ by
    change algebraMap R T r * t = r • t
    exact (Algebra.smul_def r t).symm
  exact (moduleProperty_equiv_iff k (TensorProduct.prodLeft R (S × T) S T M)).mpr
    (moduleProperty_prodRing k S T (S ⊗[R] M) (T ⊗[R] M) hs ht)

private theorem moduleProperty_iff_glueing_baseChange
    (k : Fin 4) {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    {r : ℕ} (f : Fin r → R) (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range f)).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (M : Type w) [AddCommGroup M] [Module R M] :
    moduleProperty k R M ↔ moduleProperty k S (S ⊗[R] M) ∧
      ∀ i, moduleProperty k (Localization.Away (f i)) ((Localization.Away (f i)) ⊗[R] M) := by
  refine ⟨fun h ↦ ⟨moduleProperty_baseChange k R S M h,
    fun i ↦ moduleProperty_baseChange k R (Localization.Away (f i)) M h⟩, ?_⟩
  rintro ⟨hs, hl⟩
  let T := ∀ i, Localization.Away (f i)
  have ht : moduleProperty k T (T ⊗[R] M) :=
    (moduleProperty_equiv_iff k (tensorPiLeft R (fun i ↦ Localization.Away (f i)) M)).mpr
      (moduleProperty_piRing k (fun i ↦ Localization.Away (f i)) _ hl)
  have hp := moduleProperty_baseChange_prod k R S T M hs ht
  have := faithfullyFlat_glueingProduct S f hflat hq
  have h := moduleProperties_iff_faithfullyFlat_baseChange R (S × T) M
  fin_cases k
  · exact h.1.mpr hp
  · exact h.2.1.mpr hp
  · exact h.2.2.1.mpr hp
  · exact h.2.2.2.mpr hp

private theorem moduleProperty_iff_principal_baseChange
    (k : Fin 4) {R : Type u} (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (f : R) (hflat : Module.Flat R S)
    (hq : Function.Bijective (Ideal.quotientMap
      ((Ideal.span {f}).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map))
    (M : ModuleCat.{max u v w} R) :
    moduleProperty k R M ↔
      moduleProperty k S ((ModuleCat.extendScalars (algebraMap R S)).obj M) ∧
      moduleProperty k (Localization.Away f)
        ((ModuleCat.extendScalars (algebraMap R (Localization.Away f))).obj M) := by
  have hq' : Function.Bijective (Ideal.quotientMap
      ((Ideal.span (Set.range (fun _ : Fin 1 ↦ f))).map (algebraMap R S))
      (algebraMap R S) Ideal.le_comap_map) := by
    rwa [Set.range_const]
  have h := moduleProperty_iff_glueing_baseChange k S (fun _ : Fin 1 ↦ f) hflat hq' M
  simp only [forall_const] at h
  exact h.trans (and_congr
    (moduleProperty_equiv_iff k (largeExtendScalarsEquiv S M)).symm
    (moduleProperty_equiv_iff k
      (largeExtendScalarsEquiv.{u, u, max u v w} (Localization.Away f) M)).symm)

private theorem doubleTensor_hom_ext
    {R S T M N : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra S T] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module T N]
    {φ ψ : T ⊗[S] (S ⊗[R] M) →ₗ[T] N}
    (h : ∀ m, φ ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)) =
      ψ ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m))) : φ = ψ := by
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul t x =>
    induction x using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul s m =>
      have eq : t ⊗ₜ[S] (s ⊗ₜ[R] m) =
          (algebraMap S T s * t) • ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)) := by
        calc
          t ⊗ₜ[S] (s ⊗ₜ[R] m) = t ⊗ₜ[S] (s • ((1 : S) ⊗ₜ[R] m)) := by
            simp [TensorProduct.smul_tmul']
          _ = (s • t) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m) :=
            TensorProduct.tmul_smul s t _
          _ = _ := by simp [Algebra.smul_def, TensorProduct.smul_tmul']
      rw [eq, map_smul, map_smul, h]


universe u₁ u₂ u₃ u₄

-- Tensor coherence involves several nested scalar extensions and their module structures.
set_option backward.isDefEq.respectTransparency false in
private theorem scalarComparison_isMonoidal
    {R : Type u₁} {S : Type u₂} {T : Type u₃} {U : Type u₄}
    [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (a : R →+* S) (b : R →+* T) (c : S →+* U) (d : T →+* U)
    (τ : ModuleCat.extendScalars.{u₁, u₂, max u₁ u₂ u₃ u₄ w} a ⋙
        ModuleCat.extendScalars.{u₂, u₄, max u₁ u₂ u₃ u₄ w} c ⟶
      ModuleCat.extendScalars.{u₁, u₃, max u₁ u₂ u₃ u₄ w} b ⋙ ModuleCat.extendScalars.{u₃, u₄, max
        u₁ u₂ u₃ u₄ w} d)
    (hτ : ∀ (M : ModuleCat.{max u₁ u₂ u₃ u₄ w} R) (m : M),
      τ.app M ((ModuleCat.extendRestrictScalarsAdj.{max u₁ u₂ u₃ u₄ w, u₂, u₄} c).unit.app _
        ((ModuleCat.extendRestrictScalarsAdj.{max u₁ u₂ u₃ u₄ w, u₁, u₂} a).unit.app M m)) =
      (ModuleCat.extendRestrictScalarsAdj.{max u₁ u₂ u₃ u₄ w, u₃, u₄} d).unit.app _
        ((ModuleCat.extendRestrictScalarsAdj.{max u₁ u₂ u₃ u₄ w, u₁, u₃} b).unit.app M m)) :
    letI := moduleMonoidal.{u₁, max u₁ u₂ u₃ u₄ w} R
    letI := moduleMonoidal.{u₂, max u₁ u₂ u₃ u₄ w} S
    letI := moduleMonoidal.{u₃, max u₁ u₂ u₃ u₄ w} T
    letI := moduleMonoidal.{u₄, max u₁ u₂ u₃ u₄ w} U
    letI := scalarExtensionMonoidal.{u₁, u₂, max u₁ u₂ u₃ u₄ w} a
    letI := scalarExtensionMonoidal.{u₁, u₃, max u₁ u₂ u₃ u₄ w} b
    letI := scalarExtensionMonoidal.{u₂, u₄, max u₁ u₂ u₃ u₄ w} c
    letI := scalarExtensionMonoidal.{u₃, u₄, max u₁ u₂ u₃ u₄ w} d
    τ.IsMonoidal := by
  let := moduleMonoidal.{u₁, max u₁ u₂ u₃ u₄ w} R
  let := moduleMonoidal.{u₂, max u₁ u₂ u₃ u₄ w} S
  let := moduleMonoidal.{u₃, max u₁ u₂ u₃ u₄ w} T
  let := moduleMonoidal.{u₄, max u₁ u₂ u₃ u₄ w} U
  let := scalarExtensionMonoidal.{u₁, u₂, max u₁ u₂ u₃ u₄ w} a
  let := scalarExtensionMonoidal.{u₁, u₃, max u₁ u₂ u₃ u₄ w} b
  let := scalarExtensionMonoidal.{u₂, u₄, max u₁ u₂ u₃ u₄ w} c
  let := scalarExtensionMonoidal.{u₃, u₄, max u₁ u₂ u₃ u₄ w} d
  let := a.toAlgebra
  let := b.toAlgebra
  let := c.toAlgebra
  let := d.toAlgebra
  have hτ' (M : ModuleCat.{max u₁ u₂ u₃ u₄ w} R) (m : M) :
      τ.app M ((1 : U) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m)) =
        (1 : U) ⊗ₜ[T] ((1 : T) ⊗ₜ[R] m) := hτ M m
  let F := ModuleCat.extendScalars.{u₁, u₂, max u₁ u₂ u₃ u₄ w} a ⋙ ModuleCat.extendScalars.{u₂, u₄,
    max u₁ u₂ u₃ u₄ w} c
  let G := ModuleCat.extendScalars.{u₁, u₃, max u₁ u₂ u₃ u₄ w} b ⋙ ModuleCat.extendScalars.{u₃, u₄,
    max u₁ u₂ u₃ u₄ w} d
  constructor
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    change τ.app (ModuleCat.of R (ULift.{max u₁ u₂ u₃ u₄ w} R))
        (s.down ⊗ₜ[S] ((1 : S) ⊗ₜ[R] ULift.up (1 : R))) =
      s.down ⊗ₜ[T] ((1 : T) ⊗ₜ[R] (ULift.up (1 : R) : ULift.{max u₁ u₂ u₃ u₄ w} R))
    have h := congrArg (fun x ↦ s.down • x)
      (hτ' (𝟙_ (ModuleCat.{max u₁ u₂ u₃ u₄ w} R)) (ULift.up (1 : R)))
    rw [← map_smul] at h
    change τ.app (ModuleCat.of R (ULift.{max u₁ u₂ u₃ u₄ w} R))
        ((s.down * 1) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] ULift.up (1 : R))) =
      (s.down * 1) ⊗ₜ[T] ((1 : T) ⊗ₜ[R]
        (ULift.up (1 : R) : ULift.{max u₁ u₂ u₃ u₄ w} R)) at h
    simpa only [mul_one] using h
  · intro M N
    apply (cancel_epi (Functor.OplaxMonoidal.δ F M N)).mp
    apply (cancel_mono (Functor.OplaxMonoidal.δ G M N)).mp
    simp only [F, G, Category.assoc, Functor.Monoidal.δ_μ_assoc,
      Functor.Monoidal.μ_δ, Category.comp_id]
    apply ModuleCat.hom_ext
    apply doubleTensor_hom_ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp only [TensorProduct.tmul_add, map_add, hx, hy]
    | tmul m n =>
      change (Functor.OplaxMonoidal.δ G M N)
          (τ.app (M ⊗ N) ((1 : U) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] (m ⊗ₜ[R] n)))) =
        (τ.app M ((1 : U) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] m))) ⊗ₜ[U]
          (τ.app N ((1 : U) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] n)))
      rw [hτ', hτ', hτ']
      rfl

end FormalGlueing

end

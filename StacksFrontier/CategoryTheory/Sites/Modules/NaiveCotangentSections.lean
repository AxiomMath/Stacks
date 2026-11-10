module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangent
public import StacksFrontier.RingTheory.NaiveCotangent.Defs

/-!
# The naive cotangent complex of the sections maps to the sections of `NL_{B/A}`

Let `a : A ⟶ B` be a morphism of sheaves of commutative rings on a site and let `U` be an
object of the site.  Taking sections over `U` carries the canonical polynomial presentation
`A[B] ⟶ B` of sheaves to a presentation of `B(U)` which is *not* the canonical presentation of
`B(U)` over `A(U)`: the free algebra `A[B]` is the sheafification of `W ↦ A(W)[B(W)]`, so there
is only a canonical *map*

`A(U)[B(U)] ⟶ (A[B])(U)`,

the component at `U` of the unit of sheafification, and not an isomorphism.  This file builds
from it the canonical map of two-term complexes of `B(U)`-modules

`NL_{B(U)/A(U)} ⟶ NL_{B/A}(U)`,

degreewise and together with the commutation with the two differentials.

## Main definitions

* `Stacks.NaiveCotangent.cotangentSpaceDesc` is the `S`-linear map out of the cotangent space
  `S ⊗[P] Ω[P⁄R]` of an extension classified by an additive map `P → N` into an `S`-module
  which satisfies the Leibniz rule over `P → S` and kills the image of `R`.
* `Stacks.SheafOfModules.freeAlgebraSectionsMap` is the lax comparison
  `A(U)[B(U)] ⟶ (A[B])(U)`.
* `Stacks.SheafOfModules.sectionsConormalComparison` and
  `Stacks.SheafOfModules.sectionsTensorComparison` are the two components of the canonical map
  on sections, in degrees `-1` and `0`.
* `Stacks.SheafOfModules.sectionsDifferential` is the differential of `NL_{B/A}` on sections
  over `U`, and `Stacks.SheafOfModules.naiveCotangentSections` packages the sections over `U`
  of `NL_{B/A}` as a two-term complex of `B(U)`-modules.
* `Stacks.SheafOfModules.sectionsNaiveCotangentComparison` is the canonical map
  `NL_{B(U)/A(U)} ⟶ NL_{B/A}(U)` as a chain map of two-term complexes of `B(U)`-modules.

## Main results

* `Stacks.SheafOfModules.freeAlgebraSectionsMap_presentation`: the lax comparison followed by
  the presentation `A[B] ⟶ B` on sections is evaluation `A(U)[B(U)] → B(U)`, `[b] ↦ b`; it is
  Stacks 08TU (`Stacks.Sites.FreeAlgebra.freeAlgebraSheafDesc_spec`) read at `U`.
* `Stacks.SheafOfModules.ker_le_comap_freeAlgebraSectionsMap`: consequently the lax comparison
  carries the kernel of the canonical presentation of `B(U)` over `A(U)` into the kernel `I(U)`
  of `A[B] ⟶ B` on sections.
* `Stacks.SheafOfModules.sectionsConormalComparison_mk` and
  `Stacks.SheafOfModules.sectionsTensorComparison_tmul`: the degree `-1` component sends the
  conormal class of `g` to the conormal class of `λ(g)`, and the degree `0` component sends
  `b ⊗ d p` to `b • (1 ⊗ d (λ p))`.
* `Stacks.SheafOfModules.sectionsComparison_comm`: the two components commute with the
  differential of `NL_{B(U)/A(U)}` and with the differential of `NL_{B/A}` on sections.
* `Stacks.Sites.Conormal.tensorDifferential_add`,
  `Stacks.Sites.Conormal.tensorDifferential_mul` and
  `Stacks.Sites.Conormal.tensorDifferential_coefficient`: the local section `1 ⊗ d f` of the
  middle term of a conormal sequence is a derivation in `f`.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I)
* [Stacks Project, Tag 08SX](https://stacks.math.columbia.edu/tag/08SX), the same comparison for
  the full cotangent complex.
* [Stacks Project, Tag 08TU](https://stacks.math.columbia.edu/tag/08TU), the canonical
  polynomial presentation.
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex of a morphism of sheaves of rings.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TensorProduct

universe v u w z

noncomputable section

/-! ### Maps out of the cotangent space of an extension -/

namespace Stacks.NaiveCotangent

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : Algebra.Extension R S)
  {N : Type*} [AddCommGroup N] [Module S N] (d : P.Ring →+ N)
  (hmul : ∀ x y : P.Ring, d (x * y) = algebraMap P.Ring S x • d y + algebraMap P.Ring S y • d x)
  (hbase : ∀ r : R, d (algebraMap R P.Ring r) = 0)

include hmul hbase in
/-- **Maps out of the degree `0` term.**  An additive map `d : P → N` into an `S`-module which
satisfies the Leibniz rule over the structural map `P → S` and kills the image of `R` extends to
an `S`-linear map `S ⊗[P] Ω[P⁄R] ⟶ N`, `b ⊗ d p ↦ b • d p`, on the cotangent space of the
extension `P → S`.  The module structures that `N` acquires over `P` and over `R` are the
restrictions of its `S`-module structure. -/
def cotangentSpaceDesc : P.CotangentSpace →ₗ[S] N :=
  letI : Module P.Ring N := Module.compHom N (algebraMap P.Ring S)
  letI : Module R N := Module.compHom N (algebraMap R S)
  letI : IsScalarTower R P.Ring N := IsScalarTower.of_algebraMap_smul fun r n ↦ by
    change (algebraMap P.Ring S (algebraMap R P.Ring r)) • n = (algebraMap R S r) • n
    rw [← IsScalarTower.algebraMap_apply R P.Ring S]
  letI : IsScalarTower P.Ring S N := IsScalarTower.of_algebraMap_smul fun p n ↦ rfl
  (Derivation.liftKaehlerDifferential
    { toFun := d
      map_add' := d.map_add
      map_smul' := fun r p ↦ by
        change d (r • p) = (algebraMap R S r) • d p
        rw [Algebra.smul_def, hmul, hbase, smul_zero, add_zero,
          ← IsScalarTower.algebraMap_apply R P.Ring S]
      map_one_eq_zero' := by simpa using hbase 1
      leibniz' := hmul }).liftBaseChange S

include hmul hbase in
/-- The classifying map of `d` sends `b ⊗ d p` to `b • d p`. -/
theorem cotangentSpaceDesc_tmul (b : S) (p : P.Ring) :
    cotangentSpaceDesc P d hmul hbase (b ⊗ₜ[P.Ring] KaehlerDifferential.D R P.Ring p) =
      b • d p := by
  let : Module P.Ring N := Module.compHom N (algebraMap P.Ring S)
  let : Module R N := Module.compHom N (algebraMap R S)
  let : IsScalarTower R P.Ring N := IsScalarTower.of_algebraMap_smul fun r n => by
    change (algebraMap P.Ring S (algebraMap R P.Ring r)) • n = (algebraMap R S r) • n
    rw [← IsScalarTower.algebraMap_apply R P.Ring S]
  let : IsScalarTower P.Ring S N := IsScalarTower.of_algebraMap_smul fun p n ↦ rfl
  exact congrArg (fun y : N ↦ b • y) (Derivation.liftKaehlerDifferential_comp_D _ p)

end Stacks.NaiveCotangent

/-! ### Scalars on the conormal module of an ideal -/

namespace Stacks.Sites.Conormal

/-- On the conormal module of an ideal, the action of a ring element and the action of its class
in the quotient agree. -/
theorem quotient_mk_smul_cotangent {T : Type*} [CommRing T] (I : Ideal T) (t : T)
    (z : I.Cotangent) : (Ideal.Quotient.mk I t) • z = t • z := by
  obtain ⟨y, rfl⟩ := I.toCotangent_surjective z
  rfl

end Stacks.Sites.Conormal

/-! ### Sections of a sheaf of modules, as a module over the sections of the ring -/

namespace Stacks.Sites.Conormal

/-- The sections over `U` of a sheaf of `B`-modules, as a module over the ring `B.obj.obj U` of
sections of `B`. -/
instance moduleSections {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] {B : Sheaf J CommRingCat.{w}}
    (M : _root_.SheafOfModules.{z} (Stacks.SheafOfModules.Tensor.ringSheaf B)) (U : Cᵒᵖ) :
    Module (ToType (B.obj.obj U)) (ToType (M.val.obj U)) :=
  inferInstanceAs (Module (ToType ((Stacks.SheafOfModules.Tensor.ringSheaf B).obj.obj U)) _)

end Stacks.Sites.Conormal

/-! ### The local section `1 ⊗ d f` is a derivation -/

namespace Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (R A B : Sheaf J CommRingCat.{w}) (a : R ⟶ A) (φ : A ⟶ B)
  [Presheaf.IsLocallySurjective J φ.hom] (X : Cᵒᵖ)

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [Presheaf.IsLocallySurjective J φ.hom] in
/-- The image of a section of the quotient presheaf in the sections of `B` is the image of any
of its lifts under the presentation. -/
theorem quotientToRingSheaf_mk (s : A.obj.obj X) :
    (quotientToRingSheaf J A B φ).app X (Ideal.Quotient.mk (kernelIdeal φ.hom X) s) =
      (φ.hom.app X).hom s := rfl

omit [HasWeakSheafify J CommRingCat.{w}] in
/-- **The composite of a conormal map and the sheafification unit is semilinear over the
sections of `B`.** -/
theorem toAssociatedModule_cotangentMap_smul {T : Type w} [CommRing T] (I : Ideal T)
    (f : T →+* A.obj.obj X) (hf : I ≤ Ideal.comap f (kernelIdeal φ.hom X)) (t : T)
    (c : I.Cotangent) :
    toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X
        (cotangentMap I (kernelIdeal φ.hom X) f hf (t • c)) =
      (φ.hom.app X).hom (f t) •
        toAssociatedModule.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X
          (cotangentMap I (kernelIdeal φ.hom X) f hf c) := by
  rw [← quotient_mk_smul_cotangent I t c, map_smulₛₗ]
  exact toAssociatedModule_smul.{v, u, w, z} J A B φ (conormalPresheaf φ.hom) X _ _

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The sheafification unit sends the zero section to the zero section. -/
private theorem toAssociatedModule_zero
    (M : PresheafOfModules.{w} (quotientPresheaf φ.hom ⋙ forget₂ _ RingCat)) (Y : Cᵒᵖ) :
    toAssociatedModule.{v, u, w, z} J A B φ M Y (0 : M.obj Y) = 0 := by
  simpa using toAssociatedModule_add.{v, u, w, z} J A B φ M Y (0 : M.obj Y) 0

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The local section `1 ⊗ d f` of the middle term of the conormal sequence is additive
in `f`. -/
theorem tensorDifferential_add (x y : A.obj.obj X) :
    tensorDifferential.{v, u, w, z} J R A B a φ X (x + y) =
      tensorDifferential.{v, u, w, z} J R A B a φ X x +
        tensorDifferential.{v, u, w, z} J R A B a φ X y := by
  refine Eq.trans (congrArg
    (toAssociatedModule.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X) ?_)
    (toAssociatedModule_add.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X _ _)
  refine Eq.trans (congrArg (fun ω : (differentialsPresheaf a.hom).obj X ↦
    (1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X] ω)
      (ModuleCat.Derivation.d_add (CommRingCat.KaehlerDifferential.D (a.hom.app X)) x y)) ?_
  exact TensorProduct.tmul_add _ _ _

omit [HasWeakSheafify J CommRingCat.{w}] in
/-- A section `1 ⊗ s • ω` of the middle term of the conormal sequence is `s` times `1 ⊗ ω`. -/
private theorem toAssociatedModule_one_tmul_smul (s : A.obj.obj X)
    (ω : (differentialsPresheaf a.hom).obj X) :
    toAssociatedModule.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X
        ((1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X] (s • ω)) =
      (φ.hom.app X).hom s •
        toAssociatedModule.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X
          ((1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X] ω) := by
  have h : (1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X] (s • ω) =
      (Ideal.Quotient.mk (kernelIdeal φ.hom X) s) •
        ((1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X] ω) := by
    rw [← TensorProduct.smul_tmul, ← TensorProduct.smul_tmul']
    rfl
  rw [h]
  exact toAssociatedModule_smul.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X _ _

omit [HasWeakSheafify J CommRingCat.{w}] in
/-- The local section `1 ⊗ d f` of the middle term of the conormal sequence satisfies the
Leibniz rule over the presentation on sections. -/
theorem tensorDifferential_mul (x y : A.obj.obj X) :
    tensorDifferential.{v, u, w, z} J R A B a φ X (x * y) =
      (φ.hom.app X).hom x • tensorDifferential.{v, u, w, z} J R A B a φ X y +
        (φ.hom.app X).hom y • tensorDifferential.{v, u, w, z} J R A B a φ X x := by
  refine Eq.trans (congrArg
    (toAssociatedModule.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X)
    (show (1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X]
          CommRingCat.KaehlerDifferential.d (f := a.hom.app X) (x * y) =
        (1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X]
            (x • CommRingCat.KaehlerDifferential.d (f := a.hom.app X) y) +
          (1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X]
            (y • CommRingCat.KaehlerDifferential.d (f := a.hom.app X) x) from ?_)) ?_
  · have hd : CommRingCat.KaehlerDifferential.d (f := a.hom.app X) (x * y) =
        x • CommRingCat.KaehlerDifferential.d (f := a.hom.app X) y +
          y • CommRingCat.KaehlerDifferential.d (f := a.hom.app X) x :=
      ModuleCat.Derivation.d_mul (CommRingCat.KaehlerDifferential.D (a.hom.app X)) x y
    rw [hd, TensorProduct.tmul_add]
  · refine Eq.trans (toAssociatedModule_add.{v, u, w, z} J A B φ
      (tensorPresheaf φ.hom a.hom) X _ _) ?_
    exact congrArg₂ (· + ·)
      (toAssociatedModule_one_tmul_smul.{v, u, w, z} J R A B a φ X x _)
      (toAssociatedModule_one_tmul_smul.{v, u, w, z} J R A B a φ X y _)

omit [HasWeakSheafify J CommRingCat.{w}] [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The local section `1 ⊗ d f` of the middle term of the conormal sequence vanishes on
coefficients. -/
theorem tensorDifferential_coefficient (r : R.obj.obj X) :
    tensorDifferential.{v, u, w, z} J R A B a φ X ((a.hom.app X).hom r) = 0 := by
  refine Eq.trans (congrArg
    (toAssociatedModule.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X)
    (show (1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X]
          CommRingCat.KaehlerDifferential.d (f := a.hom.app X) ((a.hom.app X).hom r) =
        0 from ?_)) ?_
  · refine Eq.trans (congrArg (fun ω : (differentialsPresheaf a.hom).obj X ↦
      (1 : A.obj.obj X ⧸ kernelIdeal φ.hom X) ⊗ₜ[A.obj.obj X] ω)
        (ModuleCat.Derivation.d_map
          (CommRingCat.KaehlerDifferential.D (a.hom.app X)) r)) ?_
    exact TensorProduct.tmul_zero _ _
  · exact toAssociatedModule_zero.{v, u, w, z} J A B φ (tensorPresheaf φ.hom a.hom) X

end Stacks.Sites.Conormal

/-! ### The comparison on sections -/

namespace Stacks.SheafOfModules

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasWeakSheafify J CommRingCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (A B : Sheaf J CommRingCat.{w}) (a : A ⟶ B) (U : Cᵒᵖ)

/-- **The lax comparison on sections.**  The free `A(U)`-algebra on the sections of `B` over `U`
maps to the sections over `U` of the free algebra sheaf `A[B]`; it is the component at `U` of
the unit of sheafification.  It is only a map: `A[B]` is the sheafification of
`W ↦ A(W)[B(W)]`. -/
def freeAlgebraSectionsMap :
    MvPolynomial (ToType (B.obj.obj U)) (ToType (A.obj.obj U)) →+*
      ToType ((freeAlgebraSheaf J A (underlyingPresheaf J B)).obj.obj U) :=
  (((toSheafification J CommRingCat.{w}).app
    (polynomialPresheaf J A (underlyingPresheaf J B))).app U).hom

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The lax comparison is compatible with the canonical presentation.**  Comparing a
polynomial over `A(U)` in the sections of `B` and then applying the presentation `A[B] ⟶ B` on
sections is evaluating it: coefficients along `a`, and the variable `[b]` at `b`.  This is
Stacks 08TU read at `U`. -/
theorem freeAlgebraSectionsMap_presentation
    (p : MvPolynomial (ToType (B.obj.obj U)) (ToType (A.obj.obj U))) :
    ((presentation J A B a (underlyingPresheaf J B) (𝟙 _)).hom.app U).hom
        (freeAlgebraSectionsMap J A B U p) =
      MvPolynomial.eval₂Hom (a.hom.app U).hom _root_.id p :=
  congrArg
    (fun t : polynomialPresheaf J A (underlyingPresheaf J B) ⟶ B.obj ↦ (t.app U).hom p)
    (freeAlgebraSheafDesc_spec J A B (underlyingPresheaf J B) a (𝟙 _))

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The lax comparison carries a variable `[b]` to the section `b` of `B`, read through the
presentation. -/
theorem freeAlgebraSectionsMap_X (b : ToType (B.obj.obj U)) :
    ((presentation J A B a (underlyingPresheaf J B) (𝟙 _)).hom.app U).hom
        (freeAlgebraSectionsMap J A B U (MvPolynomial.X b)) = b := by
  rw [freeAlgebraSectionsMap_presentation]
  exact MvPolynomial.eval₂Hom_X' _ _ b

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The lax comparison is a map of `A(U)`-algebras: it carries a constant polynomial to the
corresponding coefficient section of `A[B]`. -/
theorem freeAlgebraSectionsMap_C (r : ToType (A.obj.obj U)) :
    freeAlgebraSectionsMap J A B U (MvPolynomial.C r) =
      ((freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B)).hom.app U).hom r := rfl

/-- `B(U)` as an algebra over `A(U)`, through the sections of `a` over `U`. -/
abbrev algebraSections : Algebra (ToType (A.obj.obj U)) (ToType (B.obj.obj U)) :=
  (a.hom.app U).hom.toAlgebra

omit [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- **The lax comparison carries the kernel into the kernel.**  The kernel of the canonical
presentation `A(U)[B(U)] ⟶ B(U)` lands in the kernel `I(U)` of the presentation `A[B] ⟶ B` on
sections. -/
theorem ker_le_comap_freeAlgebraSectionsMap :
    letI := algebraSections J A B a U
    (Algebra.Generators.self (ToType (A.obj.obj U)) (ToType (B.obj.obj U))).ker ≤
      Ideal.comap (freeAlgebraSectionsMap J A B U)
        (kernelIdeal (presentation J A B a (underlyingPresheaf J B) (𝟙 _)).hom U) := by
  let := algebraSections J A B a U
  intro p hp
  rw [Algebra.Generators.ker_eq_ker_aeval_val, RingHom.mem_ker] at hp
  rw [Ideal.mem_comap, RingHom.mem_ker, freeAlgebraSectionsMap_presentation]
  exact (MvPolynomial.aeval_def _ p).symm.trans hp

/-- **The sections comparison in degree `-1`.**  The conormal module of the canonical
presentation of `B(U)` over `A(U)` maps to the sections over `U` of the conormal sheaf of
`A[B] ⟶ B`: it is the conormal map of the lax comparison, followed by the unit of
sheafification. -/
def sectionsConormalComparison :
    letI := algebraSections J A B a U
    (Algebra.Generators.self (ToType (A.obj.obj U))
        (ToType (B.obj.obj U))).toExtension.Cotangent →ₗ[ToType (B.obj.obj U)]
      ToType ((conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.obj U) := by
  letI := algebraSections J A B a U
  refine
    { toFun := fun c ↦ toAssociatedModule.{v, u, w, z} J
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))
        (conormalPresheaf (presentation J A B a (underlyingPresheaf J B) (𝟙 _)).hom) U
        (cotangentMap _ _ (freeAlgebraSectionsMap J A B U)
          (ker_le_comap_freeAlgebraSectionsMap J A B a U) c.val)
      map_add' := fun c c' ↦ ?_
      map_smul' := fun r c ↦ ?_ }
  · exact Eq.trans (congrArg (toAssociatedModule.{v, u, w, z} J
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (presentation J A B a (underlyingPresheaf J B) (𝟙 _))
      (conormalPresheaf (presentation J A B a (underlyingPresheaf J B) (𝟙 _)).hom) U)
      (map_add (cotangentMap _ _ (freeAlgebraSectionsMap J A B U)
        (ker_le_comap_freeAlgebraSectionsMap J A B a U)) c.val c'.val))
      (toAssociatedModule_add.{v, u, w, z} J
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))
        (conormalPresheaf (presentation J A B a (underlyingPresheaf J B) (𝟙 _)).hom) U _ _)
  · exact Eq.trans
      (toAssociatedModule_cotangentMap_smul.{v, u, w, z} J
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U _
        (freeAlgebraSectionsMap J A B U)
        (ker_le_comap_freeAlgebraSectionsMap J A B a U) (MvPolynomial.X r) c.val)
      (congrArg (fun s : ToType (B.obj.obj U) ↦ s • toAssociatedModule.{v, u, w, z} J
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))
        (conormalPresheaf (presentation J A B a (underlyingPresheaf J B) (𝟙 _)).hom) U
        (cotangentMap _ _ (freeAlgebraSectionsMap J A B U)
          (ker_le_comap_freeAlgebraSectionsMap J A B a U) c.val))
        (freeAlgebraSectionsMap_X J A B a U r))

/-- **The degree `-1` component sends conormal classes to conormal classes.**  The class of a
section `g` of the kernel of `A(U)[B(U)] ⟶ B(U)` goes to the class of the section `λ(g)` of the
kernel of `A[B] ⟶ B` over `U`. -/
theorem sectionsConormalComparison_mk :
    letI := algebraSections J A B a U
    ∀ g : (Algebra.Generators.self (ToType (A.obj.obj U))
      (ToType (B.obj.obj U))).toExtension.ker,
      sectionsConormalComparison.{v, u, w, z} J A B a U (Algebra.Extension.Cotangent.mk g) =
        conormalClass.{v, u, w, z} J A (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
          (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U
          ⟨freeAlgebraSectionsMap J A B U g.1,
            ker_le_comap_freeAlgebraSectionsMap J A B a U g.2⟩ := by
  let := algebraSections J A B a U
  intro g
  rfl

/-- **The sections comparison in degree `0`.**  The cotangent space of the canonical
presentation of `B(U)` over `A(U)` maps to the sections over `U` of
`B ⊗[A[B]] Ω[A[B]/A]`: it is the `B(U)`-linear extension of `p ↦ 1 ⊗ d (λ p)`. -/
def sectionsTensorComparison :
    letI := algebraSections J A B a U
    (Algebra.Generators.self (ToType (A.obj.obj U))
        (ToType (B.obj.obj U))).toExtension.CotangentSpace →ₗ[ToType (B.obj.obj U)]
      ToType ((tensorDifferentialsSheaf.{v, u, w, z} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.obj U) := by
  letI := algebraSections J A B a U
  refine Stacks.NaiveCotangent.cotangentSpaceDesc
    (Algebra.Generators.self (ToType (A.obj.obj U)) (ToType (B.obj.obj U))).toExtension
    (AddMonoidHom.mk'
      (fun p ↦ tensorDifferential.{v, u, w, z} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U
        (freeAlgebraSectionsMap J A B U p))
      (fun p q ↦ ?_)) (fun x y ↦ ?_) (fun r ↦ ?_)
  · exact Eq.trans (congrArg (tensorDifferential.{v, u, w, z} J A
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U)
      (map_add (freeAlgebraSectionsMap J A B U) p q))
      (tensorDifferential_add.{v, u, w, z} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U _ _)
  · refine Eq.trans (congrArg (tensorDifferential.{v, u, w, z} J A
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U)
      (map_mul (freeAlgebraSectionsMap J A B U) x y)) ?_
    refine Eq.trans (tensorDifferential_mul.{v, u, w, z} J A
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U _ _) ?_
    exact congrArg₂ (· + ·)
      (congrArg (fun s : ToType (B.obj.obj U) ↦ s • tensorDifferential.{v, u, w, z} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U
        (freeAlgebraSectionsMap J A B U y))
        (freeAlgebraSectionsMap_presentation J A B a U x))
      (congrArg (fun s : ToType (B.obj.obj U) ↦ s • tensorDifferential.{v, u, w, z} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U
        (freeAlgebraSectionsMap J A B U x))
        (freeAlgebraSectionsMap_presentation J A B a U y))
  · exact Eq.trans (congrArg (tensorDifferential.{v, u, w, z} J A
      (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
      (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
      (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U)
      (freeAlgebraSectionsMap_C J A B U r))
      (tensorDifferential_coefficient.{v, u, w, z} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U r)

/-- **The degree `0` component sends `b ⊗ d p` to `b • (1 ⊗ d (λ p))`.** -/
theorem sectionsTensorComparison_tmul :
    letI := algebraSections J A B a U
    ∀ (b : ToType (B.obj.obj U)) (p : (Algebra.Generators.self (ToType (A.obj.obj U))
      (ToType (B.obj.obj U))).toExtension.Ring),
      sectionsTensorComparison.{v, u, w, z} J A B a U
          (b ⊗ₜ[(Algebra.Generators.self (ToType (A.obj.obj U))
              (ToType (B.obj.obj U))).toExtension.Ring]
            KaehlerDifferential.D (ToType (A.obj.obj U))
              ((Algebra.Generators.self (ToType (A.obj.obj U))
                (ToType (B.obj.obj U))).toExtension.Ring) p) =
        b • tensorDifferential.{v, u, w, z} J A
          (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
          (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
          (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U
          (freeAlgebraSectionsMap J A B U p) := by
  let := algebraSections J A B a U
  intro b p
  exact Stacks.NaiveCotangent.cotangentSpaceDesc_tmul _ _ _ _ b p

/-- The differential of `NL_{B/A}` on sections over `U`, as a `B(U)`-linear map: the left-hand
map of the canonical conormal sequence, evaluated at `U`. -/
def sectionsDifferential :
    ToType ((conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.obj U) →ₗ[ToType (B.obj.obj U)]
      ToType ((tensorDifferentialsSheaf.{v, u, w, z} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.obj U) where
  toFun := ((conormalSequence.{v, u, w, z} J A
    (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
    (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).f.val.app U).hom
  map_add' := map_add ((conormalSequence.{v, u, w, z} J A
    (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
    (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).f.val.app U).hom
  map_smul' r x := ((conormalSequence.{v, u, w, z} J A
    (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
    (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).f.val.app U).hom.map_smul r x

/-- **The sections over `U` of `NL_{B/A}`**, as a two-term complex of `B(U)`-modules: the
sections of the conormal sheaf in degree `1`, the sections of `B ⊗[A[B]] Ω[A[B]/A]` in degree
`0`, and the sections of the left-hand map of the canonical conormal sequence as differential. -/
def naiveCotangentSections : NaiveCotangent.TwoTerm (ToType (B.obj.obj U)) where
  X₁ := ToType ((conormalSheaf.{v, u, w, z} J (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
    (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.obj U)
  X₀ := ToType ((tensorDifferentialsSheaf.{v, u, w, z} J A
    (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
    (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
    (presentation J A B a (underlyingPresheaf J B) (𝟙 _))).val.obj U)
  d := sectionsDifferential.{v, u, w, z} J A B a U

/-- **The comparison on sections is a map of complexes.**  The two components commute with the
differential `[g] ↦ 1 ⊗ dg` of `NL_{B(U)/A(U)}` and with the differential of `NL_{B/A}` on
sections over `U`. -/
theorem sectionsComparison_comm :
    letI := algebraSections J A B a U
    sectionsDifferential.{v, u, w, z} J A B a U ∘ₗ
        sectionsConormalComparison.{v, u, w, z} J A B a U =
      sectionsTensorComparison.{v, u, w, z} J A B a U ∘ₗ
        (Algebra.Generators.self (ToType (A.obj.obj U))
          (ToType (B.obj.obj U))).toExtension.cotangentComplex := by
  let := algebraSections J A B a U
  refine LinearMap.ext fun c ↦ ?_
  obtain ⟨g, rfl⟩ := Algebra.Extension.Cotangent.mk_surjective c
  have hL : sectionsDifferential.{v, u, w, z} J A B a U
      (sectionsConormalComparison.{v, u, w, z} J A B a U
        (Algebra.Extension.Cotangent.mk g)) =
      tensorDifferential.{v, u, w, z} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U
        (freeAlgebraSectionsMap J A B U g.1) :=
    Eq.trans (congrArg (sectionsDifferential.{v, u, w, z} J A B a U)
      (sectionsConormalComparison_mk.{v, u, w, z} J A B a U g))
      (conormalSequence_f_class.{v, u, w, z} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U
        ⟨freeAlgebraSectionsMap J A B U g.1,
          ker_le_comap_freeAlgebraSectionsMap J A B a U g.2⟩)
  have hR : sectionsTensorComparison.{v, u, w, z} J A B a U
      ((Algebra.Generators.self (ToType (A.obj.obj U))
        (ToType (B.obj.obj U))).toExtension.cotangentComplex
          (Algebra.Extension.Cotangent.mk g)) =
      tensorDifferential.{v, u, w, z} J A
        (freeAlgebraSheaf J A (underlyingPresheaf J B)) B
        (freeAlgebraSheafCoefficientMap J A (underlyingPresheaf J B))
        (presentation J A B a (underlyingPresheaf J B) (𝟙 _)) U
        (freeAlgebraSectionsMap J A B U g.1) := by
    rw [Algebra.Extension.cotangentComplex_mk]
    exact Eq.trans (sectionsTensorComparison_tmul.{v, u, w, z} J A B a U 1 g.1)
      (one_smul _ _)
  exact hL.trans hR.symm

/-- **The canonical map `NL_{B(U)/A(U)} ⟶ NL_{B/A}(U)`.**  The naive cotangent complex of the
sections of `a` over `U` maps canonically to the sections over `U` of the naive cotangent complex
of `a`, as a chain map of two-term complexes of `B(U)`-modules. -/
def sectionsNaiveCotangentComparison :
    letI := algebraSections J A B a U
    NaiveCotangent.ChainMap
      (NaiveCotangent.NL (Algebra.Generators.self (ToType (A.obj.obj U))
        (ToType (B.obj.obj U))))
      (naiveCotangentSections.{v, u, w, z} J A B a U) := by
  letI := algebraSections J A B a U
  exact
    { f₁ := sectionsConormalComparison.{v, u, w, z} J A B a U
      f₀ := sectionsTensorComparison.{v, u, w, z} J A B a U
      comm := sectionsComparison_comm.{v, u, w, z} J A B a U }

end Stacks.SheafOfModules

end

end

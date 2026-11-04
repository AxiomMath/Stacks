module

public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotient
public import StacksFrontier.CategoryTheory.Functor.ConjugateQuotientOfHom
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Limits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Recovering a quotient from its image under a fully faithful right adjoint

Let `R : D₁ ⥤ D₂` be a fully faithful right adjoint of `L : D₂ ⥤ D₁` between abelian categories,
let `M` be an object of `D₁` and let `c : N ≅ R M` identify an object `N` of `D₂` with the image
of `M`.  A quotient of `M`, recorded by its kernel `K'`, has an image quotient of `N`: the
composite `N ≅ R M ⟶ R(M / K')`, recorded by its kernel.  This is the shape of
`CategoryTheory.Functor.conjSubobject` at one object.

Conversely, a quotient `N ⟶ N / K` gives the quotient `M ≅ L R M ≅ L N ⟶ L(N / K)` of `M`, the
first map being the inverse of the counit, which is invertible because `R` is fully faithful.
The image under `R` of this quotient, read in `N` through `c`, is the composite of `N ⟶ N / K`
with the unit `N / K ⟶ R L (N / K)`, by the triangle identity and the naturality of the unit;
so when that unit is a monomorphism the image quotient is the quotient `N ⟶ N / K` one started
from.

## Main definitions

* `CategoryTheory.Abelian.cokernelKernelSubobjectDesc`: the monomorphism from the quotient of
  the source of a morphism by its kernel to the target.

* `CategoryTheory.Adjunction.preimageQuotientMap`: the quotient map `M ⟶ L(N / K)` attached to a
  quotient `N ⟶ N / K`, and `CategoryTheory.Adjunction.preimageQuotient` its kernel.

## Main results

* `CategoryTheory.Adjunction.comp_map_preimageQuotientMap`: the image under `R` of
  `CategoryTheory.Adjunction.preimageQuotientMap`, read through `c`, is the quotient map followed
  by the unit.
* `CategoryTheory.Adjunction.kernelSubobject_map_cokernel_π_preimageQuotientMap`: when the unit
  at the quotient is a monomorphism, the image quotient of the kernel of that quotient map is
  `K` again.
* `CategoryTheory.Adjunction.conjSubobject_kernelSubobject_preimageQuotientMap`: the same for the
  conjugate of a quotient by a comparison of functors.
* `CategoryTheory.Adjunction.conjSubobjectOfHom_preimageQuotient` and
  `CategoryTheory.Adjunction.preimageQuotient_conjSubobjectOfHom`: the two statements for the
  image quotient `CategoryTheory.Functor.conjSubobjectOfHom` along a comparison morphism.
* `CategoryTheory.Adjunction.preimageQuotient_kernelSubobject`: conversely, when `L` preserves
  monomorphisms the quotient attached to an image quotient is the quotient one started from, so
  taking image quotients is injective.
-/

@[expose] public section

open CategoryTheory.Limits

namespace CategoryTheory.Abelian

variable {C : Type*} [Category* C] [Abelian C]

/-- The quotient of the source of a morphism by its kernel maps to the target of the morphism:
the morphism factors through the projection onto that quotient. -/
noncomputable def cokernelKernelSubobjectDesc {X Y : C} (f : X ⟶ Y) :
    cokernel (kernelSubobject f).arrow ⟶ Y :=
  cokernel.desc _ f (kernelSubobject_arrow_comp f)

/-- The projection of the source of `f` onto its quotient by the kernel of `f`, followed by
`CategoryTheory.Abelian.cokernelKernelSubobjectDesc f`, is `f`. -/
@[reassoc (attr := simp)]
theorem cokernel_π_cokernelKernelSubobjectDesc {X Y : C} (f : X ⟶ Y) :
    cokernel.π (kernelSubobject f).arrow ≫ cokernelKernelSubobjectDesc f = f :=
  cokernel.π_desc _ _ _

/-- **The quotient of the source of a morphism by its kernel embeds in the target**: the
factorization through the projection onto that quotient is a monomorphism. -/
@[sga "3 IV 5.2.6" "abelian case"]
instance mono_cokernelKernelSubobjectDesc {X Y : C} (f : X ⟶ Y) :
    Mono (cokernelKernelSubobjectDesc f) := by
  let e : cokernel (kernelSubobject f).arrow ≅ Abelian.coimage f :=
    cokernel.mapIso _ _ (kernelSubobjectIso f) (Iso.refl _) (by simp)
  have he : e.hom ≫ Abelian.factorThruCoimage f = cokernelKernelSubobjectDesc f := by
    apply coequalizer.hom_ext
    simp [e, cokernelKernelSubobjectDesc, cokernel.mapIso, cokernel.map]
  rw [← he]
  infer_instance

end CategoryTheory.Abelian

namespace CategoryTheory.Adjunction

variable {D₁ : Type*} {D₂ : Type*} [Category* D₁] [Category* D₂] [Abelian D₁] [Abelian D₂]
  {L : D₂ ⥤ D₁} {R : D₁ ⥤ D₂}

/-- **The quotient of `M` attached to a quotient of `N ≅ R M`**, for a fully faithful right
adjoint `R` of `L`: the composite `M ≅ L R M ≅ L N ⟶ L(N / K)`, whose first map is the inverse of
the counit. -/
noncomputable def preimageQuotientMap (adj : L ⊣ R) [R.Full] [R.Faithful] {M : D₁} {N : D₂}
    (c : N ≅ R.obj M) (K : Subobject N) : M ⟶ L.obj (cokernel K.arrow) :=
  CategoryTheory.inv (adj.counit.app M) ≫ L.map (c.inv ≫ cokernel.π K.arrow)

/-- **The quotient of `M` attached to a quotient of `N ≅ R M`**, recorded by its kernel: the
kernel of `CategoryTheory.Adjunction.preimageQuotientMap`. -/
noncomputable def preimageQuotient (adj : L ⊣ R) [R.Full] [R.Faithful] {M : D₁} {N : D₂}
    (c : N ≅ R.obj M) (K : Subobject N) : Subobject M :=
  kernelSubobject (adj.preimageQuotientMap c K)

/-- The quotient map attached to a quotient is an epimorphism, `L` being a left adjoint. -/
instance epi_preimageQuotientMap (adj : L ⊣ R) [R.Full] [R.Faithful] {M : D₁} {N : D₂}
    (c : N ≅ R.obj M) (K : Subobject N) : Epi (adj.preimageQuotientMap c K) := by
  have := adj.isLeftAdjoint
  unfold preimageQuotientMap
  infer_instance

omit [Abelian D₁] in
/-- **The image under `R` of the quotient map attached to a quotient**, read through `c`, is the
quotient map followed by the unit of the adjunction at the quotient. -/
theorem comp_map_preimageQuotientMap (adj : L ⊣ R) [R.Full] [R.Faithful] {M : D₁} {N : D₂}
    (c : N ≅ R.obj M) (K : Subobject N) :
    c.hom ≫ R.map (adj.preimageQuotientMap c K) =
      cokernel.π K.arrow ≫ adj.unit.app (cokernel K.arrow) := by
  rw [preimageQuotientMap, Functor.map_comp, Functor.map_inv, adj.inv_counit_map]
  simp

/-- **The image quotient of the quotient attached to a quotient** is the quotient followed by the
unit: the projection `N ≅ R M ⟶ R(M / K')` onto the image of the quotient by the kernel `K'` of
`CategoryTheory.Adjunction.preimageQuotientMap`, followed by the image under `R` of the
identification of `M / K'` with `L(N / K)`, is `N ⟶ N / K ⟶ R L (N / K)`. -/
theorem comp_map_cokernel_π_preimageQuotientMap (adj : L ⊣ R) [R.Full] [R.Faithful] {M : D₁}
    {N : D₂} (c : N ≅ R.obj M) (K : Subobject N) :
    (c.hom ≫ R.map (cokernel.π (kernelSubobject (adj.preimageQuotientMap c K)).arrow)) ≫
        R.map (Abelian.cokernelKernelSubobjectIso (adj.preimageQuotientMap c K)).hom =
      cokernel.π K.arrow ≫ adj.unit.app (cokernel K.arrow) := by
  rw [Category.assoc, ← Functor.map_comp, ← Abelian.cokernelKernelSubobjectIso_inv_comp,
    Category.assoc, Iso.inv_hom_id, Category.comp_id, comp_map_preimageQuotientMap]

/-- The quotient of `M` by the kernel of the quotient map attached to `N ⟶ N / K` is
`L(N / K)`. -/
noncomputable def preimageQuotientCokernelIso (adj : L ⊣ R) [R.Full] [R.Faithful] {M : D₁}
    {N : D₂} (c : N ≅ R.obj M) (K : Subobject N) :
    cokernel (adj.preimageQuotient c K).arrow ≅ L.obj (cokernel K.arrow) :=
  Abelian.cokernelKernelSubobjectIso (adj.preimageQuotientMap c K)

/-- **A quotient whose unit is a monomorphism is the image of a quotient.**  If the unit
`N / K ⟶ R L (N / K)` is a monomorphism, the kernel of the image quotient
`N ≅ R M ⟶ R(M / K')` of the kernel `K'` of the quotient map
`CategoryTheory.Adjunction.preimageQuotientMap` attached to `K` is `K`. -/
theorem kernelSubobject_map_cokernel_π_preimageQuotientMap (adj : L ⊣ R) [R.Full] [R.Faithful]
    {M : D₁} {N : D₂} (c : N ≅ R.obj M) (K : Subobject N)
    (hK : Mono (adj.unit.app (cokernel K.arrow))) :
    kernelSubobject
        (c.hom ≫ R.map (cokernel.π (kernelSubobject (adj.preimageQuotientMap c K)).arrow)) =
      K :=
  have := hK
  (kernelSubobject_eq_of_comp_mono _ _ _
    (comp_map_cokernel_π_preimageQuotientMap adj c K)).symm.trans
    ((kernelSubobject_eq_of_comp_mono _ _ _ rfl).trans (kernelSubobject_cokernel_π K))

/-- **The quotient attached to an image quotient is the quotient one started from**, when `L`
preserves monomorphisms: for a quotient `M ⟶ M / K`, the quotient of `M` attached to the image
quotient `N ≅ R M ⟶ R(M / K)` has kernel `K`. -/
theorem preimageQuotient_kernelSubobject (adj : L ⊣ R) [R.Full] [R.Faithful]
    [L.PreservesMonomorphisms] {M : D₁} {N : D₂} (c : N ≅ R.obj M) (K : Subobject M) :
    adj.preimageQuotient c (kernelSubobject (c.hom ≫ R.map (cokernel.π K.arrow))) = K := by
  set f := c.hom ≫ R.map (cokernel.π K.arrow)
  have hfac : adj.preimageQuotientMap c (kernelSubobject f) ≫
      L.map (Abelian.cokernelKernelSubobjectDesc f) ≫ adj.counit.app (cokernel K.arrow) =
        cokernel.π K.arrow := by
    have hnat := adj.counit.naturality (cokernel.π K.arrow)
    simp only [Functor.comp_map, Functor.id_map] at hnat
    rw [preimageQuotientMap, Category.assoc, ← Category.assoc (L.map _), ← L.map_comp,
      Category.assoc, Abelian.cokernel_π_cokernelKernelSubobjectDesc, Iso.inv_hom_id_assoc,
      hnat, IsIso.inv_hom_id_assoc]
  rw [preimageQuotient, ← kernelSubobject_eq_of_comp_mono _ _ _ hfac, kernelSubobject_cokernel_π]

/-- For a comparison `e : P₂ ≅ P₁ ⋙ R` of functors into the two abelian categories, if the unit at
the quotient `P₂ M / K` is a monomorphism then the conjugate of the kernel of the quotient map
attached to `K` through `e` is `K`. -/
theorem conjSubobject_kernelSubobject_preimageQuotientMap {C : Type*} [Category* C]
    {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} (adj : L ⊣ R) [R.Full] [R.Faithful] (e : P₂ ≅ P₁ ⋙ R)
    {M : C} (K : Subobject (P₂.obj M)) (hK : Mono (adj.unit.app (cokernel K.arrow))) :
    Functor.conjSubobject e (adj.preimageQuotient (e.app M) K) = K :=
  kernelSubobject_map_cokernel_π_preimageQuotientMap adj (e.app M) K hK

/-- For a comparison morphism `e : P₂ ⟶ P₁ ⋙ R` invertible at `M`, if the unit at the quotient
`P₂ M / K` is a monomorphism then the image quotient `CategoryTheory.Functor.conjSubobjectOfHom`
of the quotient attached to `K` through `e` is `K`. -/
theorem conjSubobjectOfHom_preimageQuotient {C : Type*} [Category* C] {P₁ : C ⥤ D₁}
    {P₂ : C ⥤ D₂} (adj : L ⊣ R) [R.Full] [R.Faithful] (e : P₂ ⟶ P₁ ⋙ R) {M : C}
    (he : IsIso (e.app M)) (K : Subobject (P₂.obj M))
    (hK : Mono (adj.unit.app (cokernel K.arrow))) :
    Functor.conjSubobjectOfHom e (adj.preimageQuotient (@asIso _ _ _ _ (e.app M) he) K) = K :=
  kernelSubobject_map_cokernel_π_preimageQuotientMap adj (@asIso _ _ _ _ (e.app M) he) K hK

/-- For a comparison morphism `e : P₂ ⟶ P₁ ⋙ R` invertible at `M`, with `L` preserving
monomorphisms, the quotient attached to the image quotient
`CategoryTheory.Functor.conjSubobjectOfHom e K'` is `K'`. -/
theorem preimageQuotient_conjSubobjectOfHom {C : Type*} [Category* C] {P₁ : C ⥤ D₁}
    {P₂ : C ⥤ D₂} (adj : L ⊣ R) [R.Full] [R.Faithful] [L.PreservesMonomorphisms]
    (e : P₂ ⟶ P₁ ⋙ R) {M : C} (he : IsIso (e.app M)) (K' : Subobject (P₁.obj M)) :
    adj.preimageQuotient (@asIso _ _ _ _ (e.app M) he) (Functor.conjSubobjectOfHom e K') = K' :=
  preimageQuotient_kernelSubobject adj (@asIso _ _ _ _ (e.app M) he) K'

end CategoryTheory.Adjunction

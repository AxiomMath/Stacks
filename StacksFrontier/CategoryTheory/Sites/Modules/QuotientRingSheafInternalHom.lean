module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SheafInternalHomFirstVariable
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AlgebraBundleStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalStrictColimits
public import StacksFrontier.CategoryTheory.Monoidal.InternalHomUnitQuotient
public import StacksFrontier.CategoryTheory.Sites.Modules.QuotientRingSheafEpi

/-!
# The internal Hom out of the quotient of a sheaf of rings by a sheaf of ideals

Let `O` be a sheaf of commutative rings on a site and let `I` be a sheaf of ideals of `O`, with
quotient `O/I`. Read in sheaves of `O`-modules, the quotient map exhibits `O/I` as the cokernel
of the inclusion `I ⟶ O` of the sheaf of ideals into the free rank-one sheaf of modules. The
internal Hom is left exact in its first variable, so for every sheaf of `O`-modules `H` the
internal Hom out of the quotient is the kernel of the restriction map

`Hom_O(O, H) ⟶ Hom_O(I, H)`

along that inclusion; and `Hom_O(O, H)` is `H` itself, a local homomorphism out of the structure
sheaf being its value at the unit section. So the internal Hom out of `O/I` is the subsheaf of
`H` cut out by the condition that the associated local homomorphism kills `I`.

For `H` the quotient itself that condition is vacuous: the quotient map is an epimorphism which
annihilates `I`, so restriction along the inclusion of `I` vanishes on `Hom_O(O, O/I)`. The
sheaf of `O`-endomorphisms of `O/I` is therefore `O/I`, every local endomorphism being
multiplication by its value at the unit section.

This is the degree-zero case of the exterior-power description of self-Ext. The zeroth exterior
power of a sheaf of `O/I`-modules, formed over `O/I`, is `O/I` and not `O` — the comparison of
exterior powers over a ring and over a quotient of it is available only in positive degrees —
and the zeroth self-Ext sheaf of `O/I` is its sheaf of `O`-endomorphisms. Both sides are `O/I`,
and the map between them is the unit.

## Main definitions

* `Stacks.Sites.quotientModule`: the quotient `O/I`, read as a sheaf of `O`-modules.
* `Stacks.Sites.ihomRestrictToIdeal`: restriction along the inclusion of `I`, the map
  `Hom_O(O, H) ⟶ Hom_O(I, H)` whose kernel the internal Hom out of the quotient is.
* `Stacks.Sites.ihomQuotientModuleIsoKernel`: **the internal Hom out of `O/I` is that kernel.**
* `Stacks.Sites.ihomQuotientModuleIso`: **the internal Hom out of `O/I` is `H`** whenever the
  restriction map vanishes, and `Stacks.Sites.ihomQuotientModuleIsoSelf`: **the sheaf of
  `O`-endomorphisms of `O/I` is `O/I`.**
* `Stacks.Sites.exteriorPieceZeroIsoIhomQuotientModule`: **the degree-zero comparison** — the
  zeroth exterior power over `O/I` of a sheaf of `O/I`-modules and the sheaf of
  `O`-endomorphisms of `O/I` are the same sheaf of `O`-modules.

## Main statements

* `Stacks.Sites.quotientRingHom_app_eq_zero_of_mem`: a section of `I` dies under the quotient
  map of sheaves of rings.
* `Stacks.Sites.smul_quotientModule_eq_zero_of_mem`: **a sheaf of ideals annihilates its own
  quotient.** The action of a section of `O` on the quotient is through its image, and a section
  of `I` has image zero.
* `Stacks.Sites.ihomRestrictToIdeal_quotientModule_eq_zero`: **restriction to `I` of the local
  homomorphisms from `O` to `O/I` vanishes.**

## Implementation notes

**Why the vanishing of the restriction map is proved and not computed on sections.**
`smul_quotientModule_eq_zero_of_mem` is the statement that a section of `I` acts by zero on
`O/I`, and it would give the vanishing of the restriction map if the evaluation morphism of the
closed structure were described by a formula on local sections. It is not: the closed structure
is produced by Day's reflection theorem. The vanishing is instead a formal consequence of `O/I`
being a quotient *of the unit*: transposing the restriction map along the tensor–hom adjunction
turns it into the left unitor of `O/I` precomposed with the inclusion of `I`, and that composite
is killed by the epimorphism `O ⟶ O/I` after tensoring, which is the content of
`Stacks.MonoidalClosed.pre_app_eq_zero`. No property of `I` beyond `I ⟶ O ⟶ O/I` being zero is
used, and in particular not that `I` is an ideal rather than a submodule.

**The target types are not restated.** The quotient ring sheaf is a sheafification, so the
targets of the isomorphisms below are left to be inferred from their terms rather than written
out, as the construction of the cokernel comparison asks: over a concrete site a hand-written
copy of such a type exhausts the unifier, while elaborating the term is immediate.

## References

* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u

namespace Stacks.Sites

attribute [local implicit_reducible] CategoryTheory.sheafCompose

attribute [local instance] _root_.SheafOfModules.monoidalCategory
  _root_.SheafOfModules.symmetricCategory SheafOfModules.monoidalClosed
  SheafOfModules.monoidalPreadditiveRingSheaf

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {O : Sheaf J CommRingCat.{u}} [HasWeakSheafify J CommRingCat.{u}]

/-- **The quotient `O/I` of a sheaf of commutative rings by a sheaf of ideals, read as a sheaf
of `O`-modules**: the free rank-one sheaf of modules over `O/I`, with its scalars restricted
along the quotient map. -/
abbrev quotientModule (I : IdealSubsheaf O) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  (SheafOfModules.restrictScalars (quotientRingHom I)).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (quotientRingSheaf I)))

/-- **A section of `I` dies under the quotient map of sheaves of rings.** The kernel ideal of the
quotient map is `I`. -/
theorem quotientRingHom_app_eq_zero_of_mem (I : IdealSubsheaf O) (X : Cᵒᵖ)
    {a : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X} (ha : a ∈ I.obj X) :
    (quotientRingHom I).hom.app X a = 0 := by
  rw [← kerIdeal_quotientRingHom I] at ha
  exact RingHom.mem_ker.1 ((SheafOfModules.mem_kerIdeal _ X a).1 ha)

/-- **A sheaf of ideals annihilates its own quotient.** A section of `O` acts on `O/I` through
its image under the quotient map, and a section of `I` has image zero. -/
theorem smul_quotientModule_eq_zero_of_mem (I : IdealSubsheaf O) (X : Cᵒᵖ)
    {a : (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj X} (ha : a ∈ I.obj X)
    (h : (quotientModule I).val.obj X) : a • h = 0 := by
  refine (ModuleCat.restrictScalars.smul_def
    (RingCat.Hom.hom ((quotientRingHom I).hom.app X)) a h).trans ?_
  rw [show RingCat.Hom.hom ((quotientRingHom I).hom.app X) a = 0 from
    quotientRingHom_app_eq_zero_of_mem I X ha, zero_smul]
  rfl

section InternalHom

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The monoidal structure on `Mod(O)`**, with the universe of the sections **pinned** to the
`u` the statements below are taken at. This is `_root_.SheafOfModules.monoidalCategory`, the
localized structure named in the `attribute [local instance]` line above and the one
`Stacks.SheafOfModules.InternalHom` states its first-variable internal hom against; its sections
universe is independent of the two site universes, and here `v = u` and the sections are at `u`
as well. -/
local instance monoidalCategory :
    MonoidalCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  _root_.SheafOfModules.monoidalCategory O

/-- The symmetry of `monoidalCategory`, with the universe of the sections pinned the same way. -/
local instance symmetricCategory :
    SymmetricCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  _root_.SheafOfModules.symmetricCategory O

/-- Closedness of `monoidalCategory`, with the universe of the sections pinned the same way. -/
local instance monoidalClosed :
    MonoidalClosed (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  SheafOfModules.monoidalClosed O

/-- Bilinearity on morphisms of the tensor product of `monoidalCategory`, the last of the four
structures the `attribute [local instance]` line above names.  No universe is written out here:
the sections universe is fixed by unifying the ascribed type against the provider's. -/
local instance monoidalPreadditive :
    MonoidalPreadditive (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  SheafOfModules.monoidalPreadditiveRingSheaf O

/-- **Restriction along the inclusion of a sheaf of ideals**, the map
`Hom_O(O, H) ⟶ Hom_O(I, H)` which takes a local homomorphism out of the structure sheaf to its
restriction to `I`. -/
def ihomRestrictToIdeal (I : IdealSubsheaf O)
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  (MonoidalClosed.internalHom.flip.obj H).map (SheafOfModules.Submodule.ι I).op

/-- **Restriction to `I` of the local homomorphisms from `O` to `O/I` vanishes.** The quotient
map is an epimorphism from the free rank-one sheaf of modules, which is the monoidal unit up to
the isomorphism `SheafOfModules.unitIso`, and the inclusion of `I` composed with it is zero. -/
theorem ihomRestrictToIdeal_quotientModule_eq_zero (I : IdealSubsheaf O) :
    ihomRestrictToIdeal I (quotientModule I) = 0 :=
  have : Epi (unitToQuotientRing I) := epi_unitToQuotientRing I
  Stacks.MonoidalClosed.pre_app_eq_zero (SheafOfModules.unitIso O)
    (SheafOfModules.Submodule.ι I) (unitToQuotientRing I) (ι_comp_unitToQuotientRing I)

/-- **The internal Hom out of `O/I` is the kernel of restriction along the inclusion of `I`.**
The quotient map exhibits `O/I` as the cokernel of that inclusion, and the internal Hom is left
exact in its first variable. -/
def ihomQuotientModuleIsoKernel (I : IdealSubsheaf O)
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  Stacks.SheafOfModules.InternalHom.ihomCokernelIsoKernel O H
    (isColimitCokernelCoforkUnitToQuotientRing I)

/-- **The internal Hom out of `O/I` is `H` itself** when restriction along the inclusion of `I`
vanishes, that is, when the ideal annihilates `H`: the internal Hom out of `O/I` is the kernel of
that restriction, the kernel of a zero morphism is its source, and the internal Hom out of the
structure sheaf is `H`. -/
def ihomQuotientModuleIso (I : IdealSubsheaf O)
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (h : ihomRestrictToIdeal I H = 0) :=
  ihomQuotientModuleIsoKernel I H ≪≫ kernelIsoOfEq h ≪≫ kernelZeroIsoSource ≪≫
    Stacks.SheafOfModules.InternalHom.ihomUnitIso O H

/-- **The sheaf of `O`-endomorphisms of `O/I` is `O/I`.** Restriction to `I` of the local
homomorphisms from `O` to `O/I` vanishes, so the internal Hom out of `O/I` into `O/I` is the
internal Hom out of `O` into `O/I`, which is `O/I`. -/
def ihomQuotientModuleIsoSelf (I : IdealSubsheaf O) :=
  ihomQuotientModuleIso I (quotientModule I) (ihomRestrictToIdeal_quotientModule_eq_zero I)

/-- **The degree-zero comparison**: for a sheaf of `O/I`-modules `E`, the zeroth exterior power
of `E` over `O/I` and the sheaf of `O`-endomorphisms of `O/I` are the same sheaf of `O`-modules.

Both sides are `O/I`. The zeroth exterior power of a sheaf of modules is the free rank-one sheaf
of modules over the ring sheaf it is taken over, here `O/I` and not `O`; and the sheaf of
`O`-endomorphisms of `O/I` is `O/I`, every local endomorphism being multiplication by its value
at the unit section. -/
def exteriorPieceZeroIsoIhomQuotientModule (I : IdealSubsheaf O)
    (E : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (quotientRingSheaf I))) :=
  (SheafOfModules.restrictScalars (quotientRingHom I)).mapIso
      (SheafOfModules.algebras J E).exteriorPieceZeroIsoUnit ≪≫
    (ihomQuotientModuleIsoSelf I).symm

end InternalHom

end Stacks.Sites

end

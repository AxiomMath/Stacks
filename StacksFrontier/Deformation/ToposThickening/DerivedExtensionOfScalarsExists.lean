module

public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExtendScalarsShortExactFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverOfSize
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoverTensorExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatTwoOutOfThree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftFiniteColimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes
public import StacksFrontier.CategoryTheory.Sites.Modules.Colimits
public import StacksFrontier.Deformation.ToposThickening.DerivedComplexLift
public import StacksFrontier.Homology.CyclesShortComplex
public import StacksFrontier.Homology.TorAmplitude.Comparison

/-!
# Derived base change along a morphism of sheaves of commutative rings exists

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site. Tag 0DIZ, and with it
Tags 0DIY and 0DIX, is stated relative to a choice of derived base change
`Deformation.ComplexLift.DerivedExtensionOfScalars`, i.e. a functor on the unbounded derived
categories exhibited as the left derived functor of the degreewise extension-of-scalars functor
`Deformation.ComplexLift.extensionOfScalarsCochainComplex`. This file constructs one, so that the
choice is never vacuous: `Deformation.ComplexLift.nonempty_derivedExtensionOfScalars`.

The construction is Stacks 0794 at the class of flat sheaves of modules. Extension of scalars is
a left adjoint (Stacks 03CZ), hence additive and colimit-preserving; flat sheaves of modules
contain a zero object, are closed under binary direct sums and cover every sheaf of modules
(Stacks 03EU, 03EW); colimits along `ℕ` exist and are exact because sheaves of modules satisfy
AB5 (Stacks 03DB); and extension of scalars carries a bounded above acyclic complex of flat
sheaves of modules to an acyclic complex, which is the only hypothesis of 0794 with content.

## Main results

* `Deformation.ComplexLift.shortExact_map_extensionOfScalars`: **Stacks 03EX for extension of
  scalars**, with the module universe independent of the two site universes.
* `Deformation.ComplexLift.flatObjects_cycles_of_acyclic`: the cycles of a bounded above acyclic
  complex of flat sheaves of modules are flat.
* `Deformation.ComplexLift.acyclic_map_extensionOfScalars`: extension of scalars carries such a
  complex to an acyclic complex — the hypothesis `hFP` of Stacks 0794.
* `Deformation.ComplexLift.derivedExtensionOfScalars`: the derived base change functor, with
  `Deformation.ComplexLift.derivedExtensionOfScalarsCounit` exhibiting it as the left derived
  functor of degreewise extension of scalars.
* `Deformation.ComplexLift.isLeftDerivedFunctor_comp_derivedExtensionOfScalars`: that derived
  functor is absolute, which is what a derived adjunction (Stacks 09T5) asks of it.
* `Deformation.ComplexLift.derivedExtensionOfScalarsData`: the functor and its comparison,
  packaged as a `Deformation.ComplexLift.DerivedExtensionOfScalars`.
* `Deformation.ComplexLift.nonempty_derivedExtensionOfScalars`: a
  `Deformation.ComplexLift.DerivedExtensionOfScalars` along `f` exists.

## Implementation notes

**The flat cycles.** The hypothesis of Stacks 0794 is read through the cycles sequences
`0 ⟶ Z^i(L) ⟶ L^i ⟶ Z^j(L) ⟶ 0`, which are short exact because `L` is acyclic
(`HomologicalComplex.cyclesShortComplex_shortExact`): a functor keeping all of them short exact
carries `L` to an acyclic complex
(`CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact`), and extension of scalars
keeps a short exact sequence with flat third term short exact by Stacks 03EX. So all that is
needed is flatness of the cycles, and that is a downward induction from the bound: above the
bound the terms vanish, so the cycles do, and each step down is two out of three for flatness
(Stacks 03EY (2)) at the cycles sequence. The K-flat route — Stacks 06YQ followed by Stacks 0G7C
— would give the same thing, but 0G7C is stated at a single universe over a small site and would
collapse the universes kept free here.

**Universes.** The module universe `u` of `SheafOfModules.{u}` is independent of the site
universes `u'` and `v'`, and the two hom universes of the derived categories are independent of
all three; that is exactly the generality of
`Deformation.ComplexLift.DerivedExtensionOfScalars`, so the construction does not narrow the
statements of Tags 0DIY and 0DIZ. Keeping it needed Stacks 03EX restated: the form in the tree,
`Stacks.Sheaves.ChangeOfRings.shortExact_map_changeOfRings`, has the ring universe equal to the
site object universe. The restatement below is the same proof — extension of scalars is, on
underlying abelian sheaves, the tensor product with `O₀` placed on the left, on the nose — run at
the spelling of the underlying sheaf of rings that `Deformation.ComplexLift.ringSheafOf` uses.
The three spellings of that sheaf of rings in the tree differ only in the proof of the sheaf
condition they carry, so they are equal by proof irrelevance; instance search does not see that,
which is why the flat machinery below is invoked with its arguments explicit.

## References

* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
* [Stacks Project, Tag 03EY](https://stacks.math.columbia.edu/tag/03EY)
* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.RingedToposModules (extendScalars extendRestrictScalarsAdjunction)

noncomputable section

universe d d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}}

/-! ### Extension of scalars at the spelling of the lift statements -/

/-- Extension of scalars along `f`, over the sheaves of rings
`Deformation.ComplexLift.ringSheafOf` that the lift statements of Tags 0DIY and 0DIZ are written
with. This is `Stacks.Sheaves.RingedToposModules.extendScalars` of Stacks 03CZ, whose module
universe is already independent of the site. -/
abbrev extensionOfScalars (f : O ⟶ O₀) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀) :=
  extendScalars J f.hom (Stacks.SheafOfModules.Tensor.ringSheaf O).property
    (Stacks.SheafOfModules.Tensor.ringSheaf O₀).property

/-- Extension of scalars is a left adjoint, by Stacks 03CZ. -/
instance isLeftAdjoint_extensionOfScalars (f : O ⟶ O₀) :
    (extensionOfScalars f).IsLeftAdjoint :=
  (extendRestrictScalarsAdjunction J f.hom (Stacks.SheafOfModules.Tensor.ringSheaf O).property
    (Stacks.SheafOfModules.Tensor.ringSheaf O₀).property).isLeftAdjoint

/-- Extension of scalars is additive, being a left adjoint. -/
instance additive_extensionOfScalars (f : O ⟶ O₀) : (extensionOfScalars f).Additive :=
  (extendRestrictScalarsAdjunction J f.hom (Stacks.SheafOfModules.Tensor.ringSheaf O).property
    (Stacks.SheafOfModules.Tensor.ringSheaf O₀).property).left_adjoint_additive

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Degreewise extension of scalars is extension of scalars applied degreewise, at the spelling
above. -/
theorem extensionOfScalarsCochainComplex_eq (f : O ⟶ O₀) :
    extensionOfScalarsCochainComplex J f =
      (extensionOfScalars f).mapHomologicalComplex (ComplexShape.up ℤ) :=
  rfl

/-! ### Colimits along `ℕ` -/

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **Colimits of sheaves of modules along `ℕ` exist and are exact**, with the module universe
independent of the site: filtered colimits of sheaves of modules are exact (Stacks 03DB) at the
module universe, and `ℕ` is equivalent to a filtered category in `Type 0`, so the statement
descends to the smallest universe. -/
theorem hasExactColimitsOfShape_nat (R : Sheaf J RingCat.{u}) :
    HasExactColimitsOfShape ℕ (SheafOfModules.{u} R) := by
  have : IsFiltered (SmallModel.{u} ℕ) := IsFiltered.of_equivalence (equivSmallModel.{u} ℕ)
  have : AB5OfSize.{u, u} (SheafOfModules.{u} R) :=
    AlgebraicGeometry.SheafOfModules.instAB5SheafOfModules R
  have : AB5OfSize.{0, 0} (SheafOfModules.{u} R) := AB5OfSize_shrink _
  infer_instance

/-! ### The class of flat sheaves of modules -/

/-- Flatness of sheaves of modules, as a class of objects of `Mod(O)`: the class `P` at which
Stacks 0794 is run. -/
abbrev flatObjects (O : Sheaf J CommRingCat.{u}) :
    ObjectProperty (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  fun F ↦ AlgebraicGeometry.SheafOfModules.IsFlat.{v', u', u, u} (O := O) F

/-- A zero object is flat, which is the hypothesis `ObjectProperty.ContainsZero` of Stacks
0794. -/
instance containsZero_flatObjects (O : Sheaf J CommRingCat.{u}) :
    (flatObjects.{v', u, u'} O).ContainsZero :=
  Stacks.SheafOfModules.FlatCoproduct.containsZero_isFlat_ofSize.{v', u', u} O

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A binary direct sum of flat sheaves of modules is flat: the hypothesis `hsum` of Stacks
0794. -/
theorem flatObjects_biprod (O : Sheaf J CommRingCat.{u})
    (X Y : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (hX : flatObjects O X)
      (hY : flatObjects O Y) :
    flatObjects O (X ⊞ Y) :=
  Stacks.SheafOfModules.FlatCoproduct.isFlat_biprod_ofSize.{v', u', u} O X Y hX hY

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Every sheaf of modules is a quotient of a flat one, by Stacks 03EW: the hypothesis `hP` of
Stacks 0794, whose existentials are ordered the other way round. -/
theorem flatObjects_cover (O : Sheaf J CommRingCat.{u})
    (X : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ∃ (Y : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (_ : flatObjects O Y)
      (p : Y ⟶ X), Epi p := by
  obtain ⟨Y, p, hY, hp⟩ :=
    Stacks.SheafOfModules.FlatCover.exists_epi_from_isFlat_ofSize.{v', u', u} O X
  exact ⟨Y, hY, p, hp⟩

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A sheaf of modules isomorphic to a flat one is flat. -/
theorem flatObjects_of_iso {O : Sheaf J CommRingCat.{u}}
    {X Y : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (e : X ≅ Y)
      (hX : flatObjects O X) :
    flatObjects O Y :=
  Stacks.SheafOfModules.FlatCoproduct.isFlat_of_iso_ofSize.{v', u', u} O e hX

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- A zero sheaf of modules is flat. -/
theorem flatObjects_of_isZero {O : Sheaf J CommRingCat.{u}}
    {X : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)} (hX : IsZero X) :
      flatObjects O X := by
  obtain ⟨Z, hZ, hflat⟩ := (containsZero_flatObjects.{v', u, u'} O).exists_zero
  exact flatObjects_of_iso (hZ.iso hX) hflat

/-! ### Stacks 03EX for extension of scalars -/

/-- The functor `G ⊗_O -` on sheaves of `O`-modules preserves zero morphisms. -/
local instance preservesZeroMorphisms_sheafTensorObj (O : Sheaf J CommRingCat.{u})
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', u} O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj
      G).PreservesZeroMorphisms := by
  have : PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).obj G) := by
    have := Stacks.SheafOfModules.preservesColimits_sheafTensorObj O G
    exact PreservesColimitsOfSize.preservesFiniteColimits _
  infer_instance

/-- The functor `- ⊗_O G` on sheaves of `O`-modules preserves zero morphisms. -/
local instance preservesZeroMorphisms_sheafTensorFlipObj (O : Sheaf J CommRingCat.{u})
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u', v', u} O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).flip.obj
      G).PreservesZeroMorphisms := by
  have : PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u', v', u, u, u} O).flip.obj G) := by
    have := Stacks.SheafOfModules.preservesColimits_sheafTensorFlipObj O G
    exact PreservesColimitsOfSize.preservesFiniteColimits _
  infer_instance

/-- **Stacks 03EX for extension of scalars**, with the module universe independent of the two
site universes.

Short exactness is read on underlying abelian sheaves. There extension of scalars along `f` *is*
the tensor product with `O₀`, read as a sheaf of `O`-modules by restriction of scalars and placed
on the left: both sides sheafify the presheaf `U ↦ O₀(U) ⊗_{O(U)} G(U)`, with the tensor factors
in the same order, so no comparison of tensor products intervenes and the two composites with
`SheafOfModules.toSheaf` are the same functor. Stacks 03EX for the tensor product
(`Stacks.SheafOfModules.FlatCover.shortExact_map_sheafTensorFlipObj`) applies after the braiding
moves the fixed factor to the left, `SheafOfModules.toSheaf` is exact so it carries short
exactness, and it is faithful so it reflects it. -/
theorem shortExact_map_extensionOfScalars (f : O ⟶ O₀)
    (S : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
      (hS : S.ShortExact)
    (hflat : flatObjects O S.X₃) :
    (S.map (extensionOfScalars f)).ShortExact :=
  Stacks.FlatChangeOfRings.shortExact_map_extendScalars f S hS hflat

/-! ### The cycles of a bounded above acyclic complex of flat sheaves are flat -/

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The cycles of a complex vanishing above `a` vanish in degrees above `a`: they are a subobject
of the vanishing term. -/
private theorem isZero_cycles_of_isStrictlyLE {O : Sheaf J CommRingCat.{u}} (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
    [L.IsStrictlyLE a] {n : ℤ} (h : a < n) : IsZero (L.cycles n) :=
  (L.isZero_of_isStrictlyLE a n).of_mono (L.iCycles n)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The cycles of a complex of flat sheaves of modules which is acyclic and vanishes above `a`
are flat in every degree `a + 1 - k`, by induction on `k`.

For `k = 0` the term in degree `a + 1` vanishes, hence so do the cycles. The step down is the
cycles sequence `0 ⟶ Z^n(L) ⟶ L^n ⟶ Z^{n+1}(L) ⟶ 0`, short exact because `L` is acyclic, whose
middle and right terms are flat; two out of three for flatness (Stacks 03EY (2)) makes the left
term flat. -/
private theorem flatObjects_cycles_aux {O : Sheaf J CommRingCat.{u}} (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
      (hLE : L.IsStrictlyLE a)
    (hflat : ∀ n : ℤ, flatObjects O (L.X n)) (hac : L.Acyclic) (k : ℕ) :
    flatObjects O (L.cycles (a + 1 - k)) := by
  induction k with
  | zero => exact flatObjects_of_isZero (isZero_cycles_of_isStrictlyLE a L (by simp))
  | succ m ih =>
    refine Stacks.SheafOfModules.FlatTwoOutOfThree.isFlat_left_of_shortExact.{v', u', u} O
      (HomologicalComplex.cyclesShortComplex L (a + 1 - (↑(m + 1) : ℤ))
        (a + 1 - (↑(m + 1) : ℤ) + 1))
      (HomologicalComplex.cyclesShortComplex_shortExact L (by simp) (hac _))
      (hflat _) ?_
    rw [show a + 1 - (↑(m + 1) : ℤ) + 1 = a + 1 - m by omega]
    exact ih

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The cycles of a bounded above acyclic complex of flat sheaves of modules are flat.** -/
theorem flatObjects_cycles_of_acyclic {O : Sheaf J CommRingCat.{u}} (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
      (hLE : L.IsStrictlyLE a)
    (hflat : ∀ n : ℤ, flatObjects O (L.X n)) (hac : L.Acyclic) (n : ℤ) :
    flatObjects O (L.cycles n) := by
  rcases le_or_gt (a + 1) n with h | h
  · exact flatObjects_of_isZero (isZero_cycles_of_isStrictlyLE a L (by omega))
  · have hn : a + 1 - ((a + 1 - n).toNat : ℤ) = n := by omega
    rw [← hn]
    exact flatObjects_cycles_aux a L hLE hflat hac _

/-! ### The hypothesis of Stacks 0794 -/

/-- **Extension of scalars carries a bounded above acyclic complex of flat sheaves of modules to
an acyclic complex**: the hypothesis `hFP` of Stacks 0794.

The cycles sequences of the complex are short exact with flat third term
(`flatObjects_cycles_of_acyclic`), so Stacks 03EX keeps each of them short exact after extending
scalars, and a complex whose cycles sequences stay short exact has acyclic image. Neither
exactness of extension of scalars nor flatness of the image is used. -/
theorem acyclic_map_extensionOfScalars (f : O ⟶ O₀) (a : ℤ)
    (L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ℤ)
      (hLE : L.IsStrictlyLE a)
    (hflat : ∀ n : ℤ, flatObjects O (L.X n)) (hac : L.Acyclic) :
    (((extensionOfScalars f).mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic :=
  CochainComplex.acyclic_mapHomologicalComplex_of_cyclesShortExact (extensionOfScalars f) L
    fun _ j hij ↦ shortExact_map_extensionOfScalars f _
      (HomologicalComplex.cyclesShortComplex_shortExact L hij (hac j))
      (flatObjects_cycles_of_acyclic a L hLE hflat hac j)

/-! ### The derived base change -/

variable (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- Extension of scalars read on the homotopy category, followed by the localization to the
derived category: the functor whose left derived functor Stacks 0794 produces. -/
abbrev extensionOfScalarsHomotopy :
    HomotopyCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :=
  (extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- **Stacks 0794 applies to extension of scalars**: its left derived functor along
`Qh : K(Mod(O)) ⥤ D(Mod(O))` is defined at every object. -/
instance hasPointwiseLeftDerivedFunctor_extensionOfScalars :
    (extensionOfScalarsHomotopy.{d₀} f).HasPointwiseLeftDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) := by
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O)
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O₀)
  exact CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex
    (extensionOfScalars f) (flatObjects O) (flatObjects_biprod O) (flatObjects_cover O)
    (acyclic_map_extensionOfScalars f)

/-- **The derived base change `- ⊗_O^L O₀` along `f`**: the total left derived functor of
degreewise extension of scalars, which exists by Stacks 0794. -/
def derivedExtensionOfScalars :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) :=
  (extensionOfScalarsHomotopy f).totalLeftDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (ComplexShape.up ℤ))

/-- Its counit, on the homotopy category. -/
def derivedExtensionOfScalarsCounitHomotopy :
    DerivedCategory.Qh ⋙ derivedExtensionOfScalars.{d, d₀} f ⟶ extensionOfScalarsHomotopy f :=
  (extensionOfScalarsHomotopy f).totalLeftDerivedCounit DerivedCategory.Qh
    (HomotopyCategory.quasiIso
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) (ComplexShape.up ℤ))

/-- `derivedExtensionOfScalars f`, with the counit `derivedExtensionOfScalarsCounitHomotopy f`,
is a left derived functor of `extensionOfScalarsHomotopy f` with respect to quasi-isomorphisms. -/
instance isLeftDerivedFunctor_derivedExtensionOfScalarsCounitHomotopy :
    (derivedExtensionOfScalars.{d, d₀} f).IsLeftDerivedFunctor
      (derivedExtensionOfScalarsCounitHomotopy f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) := by
  dsimp only [derivedExtensionOfScalars, derivedExtensionOfScalarsCounitHomotopy]
  infer_instance

/-- Extension of scalars read on the homotopy category, precomposed with the homotopy quotient,
is degreewise extension of scalars followed by the localization. -/
def quotientCompExtensionOfScalarsIso :
    HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ) ⋙
        extensionOfScalarsHomotopy.{d₀} f ≅
      extensionOfScalarsCochainComplex J f ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerRight
      ((extensionOfScalars f).mapHomotopyCategoryFactors (ComplexShape.up ℤ)).symm
      DerivedCategory.Qh ≪≫
    Functor.associator ((extensionOfScalars f).mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) (ComplexShape.up ℤ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerLeft
      ((extensionOfScalars f).mapHomologicalComplex (ComplexShape.up ℤ))
      (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)))

/-- **The comparison of the derived base change with degreewise extension of scalars**: the
counit of `Deformation.ComplexLift.derivedExtensionOfScalars`, read on complexes. -/
def derivedExtensionOfScalarsCounit :
    DerivedCategory.Q ⋙ derivedExtensionOfScalars.{d, d₀} f ⟶
      extensionOfScalarsCochainComplex J f ⋙ DerivedCategory.Q :=
  Functor.whiskerRight (DerivedCategory.quotientCompQhIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))).inv
      (derivedExtensionOfScalars f) ≫
    Functor.whiskerLeft
      (HomotopyCategory.quotient (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) (derivedExtensionOfScalarsCounitHomotopy f) ≫
      (quotientCompExtensionOfScalarsIso f).hom

/-- **The comparison exhibits the derived base change as a left derived functor** along the
localization of cochain complexes at the quasi-isomorphisms: precomposition with the homotopy
quotient is fully faithful on functor categories, so the universal property along `Qh` is the
universal property along `Q`. -/
instance isLeftDerivedFunctor_derivedExtensionOfScalarsCounit :
    (derivedExtensionOfScalars.{d, d₀} f).IsLeftDerivedFunctor
      (derivedExtensionOfScalarsCounit f)
      (HomologicalComplex.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) :=
  StacksDraft.TorAmplitude.isLeftDerivedFunctor_of_homotopyCategory _
    (extensionOfScalarsHomotopy f) (quotientCompExtensionOfScalarsIso f)
    (derivedExtensionOfScalars f) (derivedExtensionOfScalarsCounitHomotopy f)
    (derivedExtensionOfScalarsCounit f) (by
      ext X
      dsimp only [derivedExtensionOfScalarsCounit, NatTrans.comp_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app]
      rw [Category.assoc, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
      simp)

/-- **The derived base change is absolute**: for *every* functor `G` out of `D(O₀)` the composite
`LF ⋙ G` is the left derived functor of `K ↦ G(O₀ ⊗_O K)`, with the whiskered comparison.

This is the hypothesis that `CategoryTheory.Adjunction.derived` — Stacks 09T5 — imposes on the
left derived functor of a derived adjunction, and it is *not* part of the data of a
`Deformation.ComplexLift.DerivedExtensionOfScalars`, which records only
`CategoryTheory.Functor.IsLeftDerivedFunctor`. It holds for the functor constructed here because
that functor is derived by resolutions: the flat objects resolve every sheaf of modules and
extension of scalars inverts the quasi-isomorphisms between the `P`-cellular complexes. -/
theorem isLeftDerivedFunctor_comp_derivedExtensionOfScalars {E : Type*} [Category E]
    (G : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ⥤ E) :
    (derivedExtensionOfScalars.{d, d₀} f ⋙ G).IsLeftDerivedFunctor
      ((Functor.associator DerivedCategory.Qh (derivedExtensionOfScalars.{d, d₀} f) G).inv ≫
        Functor.whiskerRight (derivedExtensionOfScalarsCounitHomotopy f) G)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
        (ComplexShape.up ℤ)) := by
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O)
  have := hasExactColimitsOfShape_nat (Stacks.SheafOfModules.Tensor.ringSheaf O₀)
  exact CategoryTheory.Functor.isLeftDerivedFunctor_comp_of_acyclic_mapHomologicalComplex
    (extensionOfScalars f) (flatObjects O) (flatObjects_biprod O) (flatObjects_cover O)
    (acyclic_map_extensionOfScalars f) DerivedCategory.Qh (derivedExtensionOfScalars f)
    (derivedExtensionOfScalarsCounitHomotopy f) G

/-- **The derived base change along `f`, packaged as a
`Deformation.ComplexLift.DerivedExtensionOfScalars`**: the functor constructed above together
with its comparison. -/
def derivedExtensionOfScalarsData : DerivedExtensionOfScalars.{d, d₀} f where
  baseChange := derivedExtensionOfScalars f
  comparison := derivedExtensionOfScalarsCounit f
  isLeftDerived := isLeftDerivedFunctor_derivedExtensionOfScalarsCounit f

/-- **A derived base change along `f` exists.** This is Stacks 0794 at the class of flat sheaves
of modules, so the choice of a `Deformation.ComplexLift.DerivedExtensionOfScalars` that Tags
0DIX, 0DIY and 0DIZ are stated relative to is never vacuous. -/
theorem nonempty_derivedExtensionOfScalars :
    Nonempty (DerivedExtensionOfScalars.{d, d₀} f) :=
  ⟨derivedExtensionOfScalarsData f⟩

end Deformation.ComplexLift

end

end

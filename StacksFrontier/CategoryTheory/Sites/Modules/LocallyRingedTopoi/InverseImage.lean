module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.InverseImageLocalUnit
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget
import StacksCore.Tactic.StacksAttribute

/-!
# Local ringedness is intrinsic

**Stacks 04H7.** The inverse image of a locally ringed site along a morphism of topoi is locally
ringed, and an equivalence of ringed topoi preserves and reflects local ringedness.

Both conjuncts of `AlgebraicGeometry.RingedSite.IsLocallyRinged` transport, for different
reasons, and neither is a statement about sections of the inverse image — which is what makes
the lemma possible at all, the sections of an inverse image not being describable.

Nonvanishing of `1` is the assertion that the canonical map from the initial sheaf to the
equalizer of the zero and one sections of the structure sheaf is an isomorphism. The inverse
image is left exact and is a left adjoint, so it preserves that equalizer and the initial
object; and the zero and one sections of the inverse-image structure sheaf are the images of the
zero and one sections, because the ring structure of the inverse image is the one transported
along the inverse image.

The local-unit condition is a condition on sections, and it is carried across by its categorical
form: by Stacks 04ES it is joint epimorphy of the two components of the local-unit map, and that
is what `StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedSites/InverseImageLocalUnit.lean`
transports.

## Main results

* `Stacks.Sheaves.LocalRingedness.isIso_initialTo_equalizer_map` and
  `.isIso_initialTo_equalizer_of_map`: a left exact left adjoint carries the nonvanishing
  condition of Stacks 05D7 from one parallel pair of global sections to an isomorphic one, and
  an equivalence reflects it.
* `AlgebraicGeometry.RingedSite.isLocallyRinged_inverseImage`: **Stacks 04H7 part (1)**.
* `AlgebraicGeometry.RingedToposHom.isLocallyRinged_iff_of_ringedToposEquivalence`:
  **Stacks 04H7 part (2)**.

## Implementation notes

The zero and one sections `AlgebraicGeometry.RingedSite.zeroSection` and `.oneSection` of
`StacksFrontier/CategoryTheory/Sites/Modules/LocallyRingedSites/Defs.lean` are morphisms out
of `CategoryTheory.Sheaf.terminal`, whereas the ring structure morphisms of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPullback.lean` are morphisms out of the
chosen terminal object `⊤_`. `AlgebraicGeometry.RingedSite.zeroSection_eq` and `.oneSection_eq`
identify the two, after which the transport is a computation with the transported ring
operations.

An equivalence of ringed topoi is a morphism of ringed topoi whose underlying inverse image is
an equivalence and whose structure map is an isomorphism; the inverse-image form of the
structure map is then an isomorphism too, because on underlying sheaves of sets it is
`AlgebraicGeometry.RingedToposHom.fSharpInverseImage_forget` and
`CategoryTheory.sheafCompose` reflects isomorphisms.

## References

* [Stacks Project, Tag 04H7](https://stacks.math.columbia.edu/tag/04H7)
* [Stacks Project, Tag 04EU](https://stacks.math.columbia.edu/tag/04EU)
* [Stacks Project, Tag 05D7](https://stacks.math.columbia.edu/tag/05D7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

attribute [local instance] CategoryTheory.hasInitialSheafOfTypes

/-! ### Nonvanishing of a pair of global sections, under a left exact left adjoint -/

namespace Stacks.Sheaves.LocalRingedness

universe t s w v u

section Equalizer

variable {A : Type u} [Category.{v} A] {B : Type s} [Category.{t} B]
  [HasInitial A] [HasEqualizers A] [HasInitial B] [HasEqualizers B]
  (Φ : A ⥤ B) [PreservesFiniteLimits Φ] [Φ.IsLeftAdjoint]
  {T M : A} {a₀ a₁ : T ⟶ M} {T' M' : B} {b₀ b₁ : T' ⟶ M'}
  (e₀ : Φ.obj T ≅ T') (e₁ : Φ.obj M ≅ M')
  (h₀ : Φ.map a₀ ≫ e₁.hom = e₀.hom ≫ b₀) (h₁ : Φ.map a₁ ≫ e₁.hom = e₀.hom ≫ b₁)

/-- The comparison of the two equalizers: a left exact functor preserves the equalizer, and the
two parallel pairs are isomorphic. -/
private noncomputable def equalizerMapIso :
    Φ.obj (equalizer a₀ a₁) ≅ equalizer b₀ b₁ :=
  PreservesEqualizer.iso Φ a₀ a₁ ≪≫
    HasLimit.isoOfNatIso (parallelPair.ext (F := parallelPair (Φ.map a₀) (Φ.map a₁))
      (G := parallelPair b₀ b₁) e₀ e₁ h₀ h₁)

private lemma initialTo_equalizer_eq :
    (PreservesInitial.iso Φ).inv ≫ Φ.map (initial.to (equalizer a₀ a₁)) ≫
        (equalizerMapIso Φ e₀ e₁ h₀ h₁).hom =
      initial.to (equalizer b₀ b₁) :=
  initialIsInitial.hom_ext _ _

include Φ e₀ e₁ h₀ h₁ in
/-- **Stacks 05D7 under an inverse image.** A left exact left adjoint carries the assertion that
the canonical map from the initial object to the equalizer of two global sections is an
isomorphism to the same assertion for an isomorphic pair of global sections. -/
lemma isIso_initialTo_equalizer_map (h : IsIso (initial.to (equalizer a₀ a₁))) :
    IsIso (initial.to (equalizer b₀ b₁)) := by
  rw [← initialTo_equalizer_eq Φ e₀ e₁ h₀ h₁]
  infer_instance

include Φ e₀ e₁ h₀ h₁ in
/-- An equivalence reflects the assertion of Stacks 05D7. -/
lemma isIso_initialTo_equalizer_of_map [Φ.IsEquivalence]
    (h : IsIso (initial.to (equalizer b₀ b₁))) :
    IsIso (initial.to (equalizer a₀ a₁)) := by
  have hmap : IsIso ((PreservesInitial.iso Φ).inv ≫
      Φ.map (initial.to (equalizer a₀ a₁)) ≫ (equalizerMapIso Φ e₀ e₁ h₀ h₁).hom) := by
    rwa [initialTo_equalizer_eq Φ e₀ e₁ h₀ h₁]
  have h₂ : IsIso (Φ.map (initial.to (equalizer a₀ a₁)) ≫
      (equalizerMapIso Φ e₀ e₁ h₀ h₁).hom) :=
    IsIso.of_isIso_comp_left (PreservesInitial.iso Φ).inv _
  have : IsIso (Φ.map (initial.to (equalizer a₀ a₁))) :=
    IsIso.of_isIso_comp_right _ (equalizerMapIso Φ e₀ e₁ h₀ h₁).hom
  exact isIso_of_reflects_iso _ Φ

end Equalizer

end Stacks.Sheaves.LocalRingedness

/-! ### The local-unit condition is reflected by an inverse image which is an equivalence -/

namespace Stacks.Sheaves.LocalRingedness

universe v u

section Reflect

variable {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
  {D : Type v} [Category.{v} D] {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{u})] [K.HasSheafCompose (forget RingCat.{v})]
  (Φ : Sheaf K (Type v) ⥤ Sheaf J (Type u)) [PreservesFiniteProducts Φ]
  (R : Sheaf K RingCat.{v})

/-- The inverse form of the identification of the local-unit map of an inverse image. -/
lemma localUnitBranch_pullback_inv (b : Bool) :
    localUnitBranch (pullbackRingSheaf J Φ R) b ≫ (pullbackRingSqIso J Φ R).inv =
      (pullbackRingSqIso J Φ R).inv ≫ Φ.map (localUnitBranch R b) := by
  rw [← (Iso.inv_comp_eq (pullbackRingSqIso J Φ R)).2 (map_localUnitBranch_pullback J Φ R b),
    Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Reflect

section ReflectCommRing

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {D : Type v} [Category.{v} D] {K : GrothendieckTopology D}
  (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type v)))
  (O : Sheaf K CommRingCat.{v}) [f.inverseImage.IsEquivalence]

/-- **Stacks 04ES, condition (3), reflected by an inverse image which is an equivalence.** -/
theorem condition3_of_inverseImage
    (h : Stacks.Sheaves.LocallyRingedSite.Condition3 ((inverseImageCommRingFunctor f).obj O)) :
    Stacks.Sheaves.LocallyRingedSite.Condition3 O := by
  have := f.preservesFiniteLimits
  refine (jointlyEpi_localUnitBranch_iff_condition3 O).1
    (JointlyEpi.of_map f.inverseImage ?_)
  refine ((jointlyEpi_localUnitBranch_iff_condition3
      ((inverseImageCommRingFunctor f).obj O)).2 h).conj
    (pullbackRingSqIso J f.inverseImage (SheafOfModules.Tensor.ringSheaf O)).symm
    (localUnitBranch_pullback_inv J f.inverseImage (SheafOfModules.Tensor.ringSheaf O) false)
    (localUnitBranch_pullback_inv J f.inverseImage (SheafOfModules.Tensor.ringSheaf O) true)

/-- **Stacks 04ES, condition (1), reflected by an inverse image which is an equivalence.** -/
theorem locallyEitherUnit_of_inverseImage
    (h : AlgebraicGeometry.RingedSite.LocallyEitherUnit
      ((inverseImageCommRingFunctor f).obj O)) :
    AlgebraicGeometry.RingedSite.LocallyEitherUnit O :=
  (Stacks.Sheaves.LocallyRingedSite.condition1_iff_condition3 O).2
    (condition3_of_inverseImage f O
      ((Stacks.Sheaves.LocallyRingedSite.condition1_iff_condition3 _).1 h))

end ReflectCommRing

end Stacks.Sheaves.LocalRingedness

/-! ### The zero and one sections as ring structure morphisms -/

namespace AlgebraicGeometry.RingedSite

universe w v u w' v' u'

section Sections

variable (X : RingedSite.{u, v, w}) [X.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- The zero of the structure sheaf, as a morphism out of the chosen terminal sheaf of sets.
Its result type is the underlying sheaf of sets of the structure sheaf, which is the underlying
sheaf of sets of the underlying sheaf of rings on the nose. -/
noncomputable def structureZeroHom :
    ⊤_ (Sheaf X.J (Type w)) ⟶ underlyingStructureSheaf X :=
  Sheaf.ringZeroHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)

/-- The unit of the structure sheaf, as a morphism out of the chosen terminal sheaf of sets. -/
noncomputable def structureOneHom :
    ⊤_ (Sheaf X.J (Type w)) ⟶ underlyingStructureSheaf X :=
  Sheaf.ringOneHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- On sections over `Z`, `structureZeroHom X` sends each section of the terminal sheaf to the
zero of the ring of sections of the structure sheaf over `Z`. -/
@[simp]
lemma sectionsFunctor_map_structureZeroHom (Z : X.Cᵒᵖ)
    (p : (Sheaf.sectionsFunctor X.J Z).obj (⊤_ (Sheaf X.J (Type w)))) :
    (Sheaf.sectionsFunctor X.J Z).map (structureZeroHom X) p =
      Sheaf.ringZeroObj ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)
        (Sheaf.sectionsFunctor X.J Z) := rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- On sections over `Z`, `structureOneHom X` sends each section of the terminal sheaf to the
unit of the ring of sections of the structure sheaf over `Z`. -/
@[simp]
lemma sectionsFunctor_map_structureOneHom (Z : X.Cᵒᵖ)
    (p : (Sheaf.sectionsFunctor X.J Z).obj (⊤_ (Sheaf X.J (Type w)))) :
    (Sheaf.sectionsFunctor X.J Z).map (structureOneHom X) p =
      Sheaf.ringOneObj ((Stacks.SheafOfModules.Tensor.ringSheaf (J := X.J)) X.O)
        (Sheaf.sectionsFunctor X.J Z) := rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The zero section of the structure sheaf is the zero of its underlying sheaf of rings. -/
lemma zeroSection_eq :
    zeroSection X =
      terminal.from (Sheaf.terminal X.J Types.isTerminalPUnit.{w}) ≫ structureZeroHom X :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] in
/-- The one section of the structure sheaf is the unit of its underlying sheaf of rings. -/
lemma oneSection_eq :
    oneSection X =
      terminal.from (Sheaf.terminal X.J Types.isTerminalPUnit.{w}) ≫ structureOneHom X :=
  Sheaf.hom_ext_sections fun _ _ ↦ rfl

end Sections

/-! ### Local ringedness transfers along an isomorphism of structure sheaves -/

section Iso

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  {O P : Sheaf J CommRingCat.{u}} (e : O ≅ P)

include e in
/-- The local-unit condition transfers along an isomorphism of structure sheaves. -/
lemma locallyEitherUnit_of_iso (h : LocallyEitherUnit O) : LocallyEitherUnit P := by
  intro U g
  obtain ⟨S, hS, hP⟩ := h U ((e.inv.hom.app (op U)) g)
  refine ⟨S, hS, fun V k hk ↦ ?_⟩
  have hid : ∀ x : P.obj.obj (op U), (e.hom.hom.app (op U)) ((e.inv.hom.app (op U)) x) = x :=
    fun x ↦ ConcreteCategory.congr_hom
      (congrArg (fun m : P ⟶ P ↦ m.hom.app (op U)) e.inv_hom_id) x
  have key : ∀ x : P.obj.obj (op U),
      (e.hom.hom.app (op V)) ((O.obj.map k.op) ((e.inv.hom.app (op U)) x)) =
        (P.obj.map k.op) x := by
    intro x
    refine Eq.trans ?_ (congrArg (P.obj.map k.op) (hid x))
    exact (ConcreteCategory.congr_hom (e.hom.hom.naturality k.op).symm
      ((e.inv.hom.app (op U)) x)).symm
  rcases hP k hk with hu | hu
  · left
    rw [← key g]
    exact hu.map (e.hom.hom.app (op V)).hom
  · right
    rw [← key (1 - g), map_sub, map_one]
    exact hu.map (e.hom.hom.app (op V)).hom

include e in
/-- Nonvanishing of `1` transfers along an isomorphism of structure sheaves. -/
lemma isIso_oneIsNeverZero_of_iso
    (h : IsIso (oneIsNeverZero ({ C := C, J := J, O := O } : RingedSite.{u, u, u}))) :
    IsIso (oneIsNeverZero ({ C := C, J := J, O := P } : RingedSite.{u, u, u})) := by
  have := (Adjunction.id (C := Sheaf J (Type u))).isLeftAdjoint
  refine Stacks.Sheaves.LocalRingedness.isIso_initialTo_equalizer_map
    (𝟭 (Sheaf J (Type u))) (Iso.refl _)
    ((sheafCompose J (forget CommRingCat.{u})).mapIso e) ?_ ?_ h
  · refine Sheaf.hom_ext_sections fun Y s ↦ ?_
    rw [Functor.map_comp_apply]
    exact map_zero (e.hom.hom.app Y).hom
  · refine Sheaf.hom_ext_sections fun Y s ↦ ?_
    rw [Functor.map_comp_apply]
    exact map_one (e.hom.hom.app Y).hom

include e in
/-- **Local ringedness is invariant under an isomorphism of structure sheaves.** -/
lemma isLocallyRinged_of_iso
    (h : IsLocallyRinged ({ C := C, J := J, O := O } : RingedSite.{u, u, u})) :
    IsLocallyRinged ({ C := C, J := J, O := P } : RingedSite.{u, u, u}) :=
  ⟨isIso_oneIsNeverZero_of_iso e h.1, locallyEitherUnit_of_iso e h.2⟩

end Iso

/-! ### Local ringedness passes to an inverse image -/

section InverseImage

variable (C : Type u) [Category.{u} C] (J : GrothendieckTopology C)
  (Y : RingedSite.{v, v, v})
  (f : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf Y.J (Type v)))

/-- The inverse image of the terminal sheaf of sets is terminal, the inverse image of a
morphism of topoi being left exact. -/
private noncomputable def inverseImageTerminalIso :
    f.inverseImage.obj (Sheaf.terminal Y.J Types.isTerminalPUnit.{v}) ≅
      Sheaf.terminal J Types.isTerminalPUnit.{u} :=
  have := f.preservesFiniteLimits
  (IsTerminal.isTerminalObj f.inverseImage _
      (Sheaf.isTerminalTerminal Y.J Types.isTerminalPUnit.{v})).uniqueUpToIso
    (Sheaf.isTerminalTerminal J Types.isTerminalPUnit.{u})

/-- The underlying sheaf of sets of an inverse-image structure sheaf is the inverse image of the
underlying sheaf of sets, on the nose. -/
private noncomputable def inverseImageStructureIso :
    f.inverseImage.obj (underlyingStructureSheaf Y) ≅
      underlyingStructureSheaf
        ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } :
          RingedSite.{u, u, u}) :=
  Iso.refl _

private lemma structureZeroHom_inverseImage :
    f.inverseImage.map (structureZeroHom Y) ≫ (inverseImageStructureIso C J Y f).hom =
      terminal.from (f.inverseImage.obj (⊤_ (Sheaf Y.J (Type v)))) ≫
        structureZeroHom
          ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } :
            RingedSite.{u, u, u}) := by
  have := f.preservesFiniteLimits
  refine Sheaf.hom_ext_sections fun Z t ↦ ?_
  rw [Functor.map_comp_apply, Functor.map_comp_apply, Functor.map_terminalFrom_apply]
  exact congrArg ((f.inverseImage ⋙ Sheaf.sectionsFunctor J Z).map
      (Sheaf.ringZeroHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)))
    (Subsingleton.elim (α := (f.inverseImage ⋙ Sheaf.sectionsFunctor J Z).obj
      (⊤_ (Sheaf Y.J (Type v)))) t default)

private lemma structureOneHom_inverseImage :
    f.inverseImage.map (structureOneHom Y) ≫ (inverseImageStructureIso C J Y f).hom =
      terminal.from (f.inverseImage.obj (⊤_ (Sheaf Y.J (Type v)))) ≫
        structureOneHom
          ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } :
            RingedSite.{u, u, u}) := by
  have := f.preservesFiniteLimits
  refine Sheaf.hom_ext_sections fun Z t ↦ ?_
  rw [Functor.map_comp_apply, Functor.map_comp_apply, Functor.map_terminalFrom_apply]
  exact congrArg ((f.inverseImage ⋙ Sheaf.sectionsFunctor J Z).map
      (Sheaf.ringOneHom ((Stacks.SheafOfModules.Tensor.ringSheaf (J := Y.J)) Y.O)))
    (Subsingleton.elim (α := (f.inverseImage ⋙ Sheaf.sectionsFunctor J Z).obj
      (⊤_ (Sheaf Y.J (Type v)))) t default)

private lemma zeroSection_square :
    f.inverseImage.map (zeroSection Y) ≫ (inverseImageStructureIso C J Y f).hom =
      (inverseImageTerminalIso C J Y f).hom ≫
        zeroSection ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } :
          RingedSite.{u, u, u}) := by
  rw [zeroSection_eq Y, zeroSection_eq
      ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } : RingedSite.{u, u, u}),
    Functor.map_comp, Category.assoc, structureZeroHom_inverseImage, ← Category.assoc,
    ← Category.assoc]
  exact congrArg (fun m ↦ m ≫ structureZeroHom
    ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } : RingedSite.{u, u, u}))
    (terminalIsTerminal.hom_ext _ _)

private lemma oneSection_square :
    f.inverseImage.map (oneSection Y) ≫ (inverseImageStructureIso C J Y f).hom =
      (inverseImageTerminalIso C J Y f).hom ≫
        oneSection ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } :
          RingedSite.{u, u, u}) := by
  rw [oneSection_eq Y, oneSection_eq
      ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } : RingedSite.{u, u, u}),
    Functor.map_comp, Category.assoc, structureOneHom_inverseImage, ← Category.assoc,
    ← Category.assoc]
  exact congrArg (fun m ↦ m ≫ structureOneHom
    ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } : RingedSite.{u, u, u}))
    (terminalIsTerminal.hom_ext _ _)

/-- Nonvanishing of `1` passes to an inverse image: the inverse image preserves the initial
sheaf and the equalizer of the zero and one sections, and carries one to the other. -/
lemma isIso_oneIsNeverZero_inverseImage (h : IsIso (oneIsNeverZero Y)) :
    IsIso (oneIsNeverZero
      ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } :
        RingedSite.{u, u, u})) :=
  have := f.preservesFiniteLimits
  have := f.adj.isLeftAdjoint
  Stacks.Sheaves.LocalRingedness.isIso_initialTo_equalizer_map f.inverseImage
    (inverseImageTerminalIso C J Y f) (inverseImageStructureIso C J Y f)
    (zeroSection_square C J Y f) (oneSection_square C J Y f) h

/-- **Stacks Project, Tag 04H7, part (1).** The inverse image of a locally ringed site by a
morphism of topoi is locally ringed. -/
@[stacks 04H7 "part (1)"]
theorem isLocallyRinged_inverseImage (hY : IsLocallyRinged Y) :
    IsLocallyRinged
      ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } :
        RingedSite.{u, u, u}) :=
  ⟨isIso_oneIsNeverZero_inverseImage C J Y f hY.1,
    Stacks.Sheaves.LocalRingedness.locallyEitherUnit_inverseImage f Y.O hY.2⟩

/-- Nonvanishing of `1` is reflected by an inverse image which is an equivalence. -/
lemma isIso_oneIsNeverZero_of_inverseImage [f.inverseImage.IsEquivalence]
    (h : IsIso (oneIsNeverZero
      ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } :
        RingedSite.{u, u, u}))) :
    IsIso (oneIsNeverZero Y) :=
  have := f.preservesFiniteLimits
  have := f.adj.isLeftAdjoint
  Stacks.Sheaves.LocalRingedness.isIso_initialTo_equalizer_of_map f.inverseImage
    (inverseImageTerminalIso C J Y f) (inverseImageStructureIso C J Y f)
    (zeroSection_square C J Y f) (oneSection_square C J Y f) h

/-- Local ringedness is reflected by an inverse image which is an equivalence. -/
lemma isLocallyRinged_of_inverseImage [f.inverseImage.IsEquivalence]
    (h : IsLocallyRinged
      ({ C := C, J := J, O := (inverseImageCommRingFunctor f).obj Y.O } :
        RingedSite.{u, u, u})) :
    IsLocallyRinged Y :=
  ⟨isIso_oneIsNeverZero_of_inverseImage C J Y f h.1,
    Stacks.Sheaves.LocalRingedness.locallyEitherUnit_of_inverseImage f Y.O h.2⟩

end InverseImage

end AlgebraicGeometry.RingedSite

/-! ### Invariance under an equivalence of ringed topoi -/

namespace AlgebraicGeometry.RingedToposHom

universe w v u w' v' u'

variable (X : RingedTopos.{u, u, u}) (Y : RingedTopos.{v, v, v})

/-- **Stacks Project, Tag 04H7, part (2).** An equivalence of ringed topoi preserves and
reflects local ringedness. -/
@[stacks 04H7 "part (2)"]
theorem isLocallyRinged_iff_of_ringedToposEquivalence (f : RingedToposHom X Y)
    [f.toToposHom.inverseImage.IsEquivalence] [IsIso f.fSharp] :
    RingedSite.IsLocallyRinged ({ C := Y.C, J := Y.J, O := Y.O } : RingedSite.{v, v, v}) ↔
      RingedSite.IsLocallyRinged ({ C := X.C, J := X.J, O := X.O } : RingedSite.{u, u, u}) := by
  have := f.toToposHom.adj.isEquivalence_right_of_isEquivalence_left
  have hforget : IsIso (X.forgetRing.map f.fSharpInverseImage) := by
    rw [fSharpInverseImage_forget f]
    exact IsIso.comp_isIso'
      (inferInstance : IsIso (f.toToposHom.inverseImage.map (Y.forgetRing.map f.fSharp)))
      (inferInstance : IsIso (f.toToposHom.adj.counit.app (X.forgetRing.obj X.O)))
  have : IsIso f.fSharpInverseImage := isIso_of_reflects_iso _ X.forgetRing
  exact ⟨fun hY ↦ RingedSite.isLocallyRinged_of_iso (asIso f.fSharpInverseImage)
      (RingedSite.isLocallyRinged_inverseImage X.C X.J
        ({ C := Y.C, J := Y.J, O := Y.O } : RingedSite.{v, v, v}) f.toToposHom hY),
    fun hX ↦ RingedSite.isLocallyRinged_of_inverseImage X.C X.J
      ({ C := Y.C, J := Y.J, O := Y.O } : RingedSite.{v, v, v}) f.toToposHom
      (RingedSite.isLocallyRinged_of_iso (asIso f.fSharpInverseImage).symm hX)⟩

end AlgebraicGeometry.RingedToposHom

end

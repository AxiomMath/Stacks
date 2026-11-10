module

public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FinitePushforwardCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Bridge.SchemeBridge
public import StacksCore.Tactic.StacksAttribute

/-!
# [Stacks, Tag 087T]: coherent modules on a closed subscheme

For a closed immersion `i : Z ⟶ X` of locally Noetherian schemes, direct image is an equivalence
from the coherent modules on `Z` onto the coherent modules on `X` that the ideal of `Z`
annihilates — and the equivalence is the one induced by direct image, not an abstract one.

## Main definitions

* `CoherentAnnihilatedModules i`: the coherent `𝒪_X`-modules annihilated by the kernel ideal of
  `i`, tested on affine opens. This is the category of [Stacks, Tag 087T], verbatim.
* `coherentPushforward`: direct image as a functor into that category.

## Main results

* `annihilates_of_annihilates_affineOpens`: **the bridge**. Annihilation tested on affine opens
  implies annihilation over *every* open. This is what the essential-image criterion of
  [Stacks, Tag 08KS] consumes, and 087T's category is stated with the affine test.
* `exists_isCoherent_pushforward_iso`: **essential surjectivity with coherence** — every coherent
  module annihilated by the ideal is the direct image of a *coherent* module on `Z`.
* `coherentPushforwardEquivalence`: [Stacks, Tag 087T].

## Implementation notes

**Nothing here is a new theorem; the content is a composition.** All four ingredients are
already in the library; this file puts them together:

1. direct image along a closed immersion of schemes is full and faithful —
   `Stacks.Tag08KS.full_schemeModulesPushforward_of_isClosedImmersion` and its faithful sibling;
2. an `𝒪_X`-module is a direct image exactly when the kernel ideal annihilates it —
   `Stacks.Tag08KS.essImage_pushforward_iff_of_isClosedImmersion`, scheme-level and with no
   Noetherian hypothesis, together with the form that produces the unit isomorphism,
   `Stacks.Tag08KS.isIso_unit_app_iff_of_isClosedImmersion`;
3. the pullback of a coherent module to a locally Noetherian scheme is coherent —
   `AlgebraicGeometry.isCoherent_pullback` ([Stacks, Tag 0EBF]);
4. the direct image of a coherent module along a finite morphism to a locally Noetherian scheme
   is coherent —
   `Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite`
   ([Stacks, Tag 01Y6]), applicable because a closed immersion is finite.

Essential surjectivity is then not an existence argument at all: the module on `Z` is the
*pullback* `i^*A`, which is coherent by (3), and the unit `A ⟶ i_*i^*A` is an isomorphism by (2).

**The one genuinely missing step was the affine-to-arbitrary-open bridge.** Criterion (2)
quantifies over *every* open of `X`, whereas 087T's category — and every consumer in this
development, `Stacks.AlgebraicGeometry.Tag01YEStalkBridge` included — tests annihilation on affine
opens against `Scheme.Hom.ker`. The passage back needs `Scheme.Hom.ker_apply` (hence
`QuasiCompact i`, automatic for a closed immersion) plus separatedness of the module sheaf: a
section is zero once its restrictions to a basis of affine opens are, and restriction is
semilinear, so an affine neighbourhood of each point suffices. The forward passage is free from
`Scheme.Hom.ideal_ker_le`, which needs no hypothesis at all.

**The equivalence is assembled, not constructed.** `ObjectProperty.lift` gives the functor,
`ObjectProperty.liftCompιIso` is `Iso.refl` and hence discharges the second component of the
statement outright, and `Functor.asEquivalence` turns full + faithful + essentially surjective into
an equivalence. Fullness of the lift comes from `Functor.Full.of_comp_faithful`, since the
composite with the inclusion is `ι ⋙ i_*`.

**Spelling.** `SheafOfModules.IsCoherent` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean` is used
throughout — the class that dot notation `M.IsCoherent` resolves to, and the one that
`isCoherent_pullback` and `isCoherent_pushforward_of_isFinite` are stated over. The other
`IsCoherent` of
this tree, `Stacks.SheafOfModules.IsCoherent`, carries `Stacks.SheafOfModules.CoherentModules`;
the two are bridged by `AlgebraicGeometry.CoherentAbelian.stacksIsCoherent_of_isCoherent`, so a
consumer sitting at the other spelling can cross.

## References

* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.Tag087TCoherentImage

variable {X Z : Scheme.{u}} (i : Z ⟶ X)

/-! ### The annihilation condition, on affine opens and on all opens -/

/-- Annihilation of a module by the kernel ideal of `i`, tested on affine opens. This is the
second conjunct of the defining condition of `CoherentAnnihilatedModules` below, the category
in the statement of Tag 087T, verbatim. -/
def AnnihilatedByKer (M : X.Modules) : Prop :=
  ∀ U : X.affineOpens, ∀ a : Γ(X, U.1), a ∈ i.ker.ideal U → ∀ m : Γ(M, U.1), a • m = 0

/-- Restriction of a section killed by `i` is killed by `i`: naturality of `Scheme.Hom.app`.

Stated with the scalar bound at the `Γ(X, U)` spelling, because the proof rewrites with
`Scheme.Hom.naturality`, which is stated there. A caller holding the scalar at the
`X.ringCatSheaf.obj` spelling may still apply it — the two types are definitionally equal and
application elaboration crosses them, whereas `rw` does not. -/
private theorem app_map_eq_zero {U V : Opens X} (hVU : V ≤ U) (a : Γ(X, U))
    (ha : i.app U a = 0) :
    i.app V (X.presheaf.map (homOfLE hVU).op a) = 0 := by
  rw [← ConcreteCategory.comp_apply, i.naturality (homOfLE hVU).op,
    ConcreteCategory.comp_apply, ha, map_zero]

/-- Restriction of sections of a module sheaf is semilinear, so a product that vanishes after
restriction gives a restricted product equal to the restriction of zero.

Everything is bound at the `X.ringCatSheaf.obj` spelling of the scalars, which is the one
`PresheafOfModules.map_smul` is stated over; a caller holding the restricted scalar as
`X.presheaf.map _ a` supplies it by definitional equality. -/
private theorem map_smul_eq_map_zero (M : X.Modules) {U V : Opens X} (hVU : V ≤ U)
    (a : X.ringCatSheaf.obj.obj (op U)) (m : M.val.obj (op U))
    (h : (X.ringCatSheaf.obj.map (homOfLE hVU).op a) • (M.val.map (homOfLE hVU).op m) = 0) :
    M.val.map (homOfLE hVU).op (a • m) = M.val.map (homOfLE hVU).op 0 := by
  rw [M.val.map_smul (homOfLE hVU).op a m, h, map_zero]

/-- **The bridge: annihilation on affine opens implies annihilation over every open.**

The test on arbitrary opens is what [Stacks, Tag 08KS]'s essential-image criterion consumes,
while `Scheme.Hom.ker` — and hence 087T's category — is indexed by affine opens. For a point of
an arbitrary open, choose an affine open neighbourhood inside it; the restriction of the scalar
still kills `i`, by naturality, and restriction of sections is semilinear, so the restricted
product vanishes. Separatedness of the module sheaf then gives the vanishing over the whole
open. -/
theorem annihilates_of_annihilates_affineOpens [QuasiCompact i] {M : X.Modules}
    (h : AnnihilatedByKer i M) (U : Opens X) (a : X.ringCatSheaf.obj.obj (op U))
    (ha : a ∈ RingHom.ker (i.toLRSHom.c.app (op U)).hom) (m : M.val.obj (op U)) :
    a • m = 0 := by
  have ha' : i.app U a = 0 := RingHom.mem_ker.mp ha
  refine TopCat.Presheaf.IsSheaf.section_ext (Scheme.Modules.isSheaf M) (U := op U) ?_
  intro x hx
  obtain ⟨-, ⟨V, hVaff, rfl⟩, hxV, hVU⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  have hVU' : V ≤ U := hVU
  refine ⟨V, hVU', hxV, ?_⟩
  have hmem : (X.presheaf.map (homOfLE hVU').op a) ∈ i.ker.ideal ⟨V, hVaff⟩ := by
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    exact app_map_eq_zero i hVU' a ha'
  exact map_smul_eq_map_zero M hVU' a m
    (h ⟨V, hVaff⟩ (X.presheaf.map (homOfLE hVU').op a) hmem (M.val.map (homOfLE hVU').op m))

/-- The direct image of any module is annihilated by the kernel ideal of `i`, with no coherence
or Noetherian hypothesis: it lies in the essential image of direct image by construction, and
[Stacks, Tag 08KS] identifies that essential image with the annihilated modules. The affine test
follows from the test on all opens because `Scheme.Hom.ideal_ker_le` holds unconditionally. -/
theorem annihilatedByKer_pushforward [AlgebraicGeometry.IsClosedImmersion i] (G : Z.Modules) :
    AnnihilatedByKer i ((Scheme.Modules.pushforward i).obj G) := by
  have hall := (Stacks.Tag08KS.essImage_pushforward_iff_of_isClosedImmersion i
    ((Scheme.Modules.pushforward i).obj G)).mp ⟨G, ⟨Iso.refl _⟩⟩
  intro U a ha m
  exact hall U.1 a (Scheme.Hom.ideal_ker_le i U ha) m

/-! ### Essential surjectivity, with coherence -/

/-- **Every coherent module annihilated by the ideal of `Z` is the direct image of a coherent
module on `Z`** — and the module on `Z` is the pullback `i^*A`, so nothing is chosen.

This is the half of [Stacks, Tag 087T] that the dévissage of [Stacks, Tag 01YE] consumes. The
coherence of the pullback is [Stacks, Tag 0EBF] and needs only `Z` locally Noetherian; the
isomorphism is the unit of `i^* ⊣ i_*`, which [Stacks, Tag 08KS] makes invertible exactly under
the annihilation hypothesis. -/
theorem exists_isCoherent_pushforward_iso [AlgebraicGeometry.IsClosedImmersion i]
    [IsLocallyNoetherian Z] (A : X.Modules) [A.IsCoherent] (hA : AnnihilatedByKer i A) :
    ∃ G : Z.Modules, G.IsCoherent ∧
      Nonempty ((Scheme.Modules.pushforward i).obj G ≅ A) := by
  have hiso : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A) :=
    (Stacks.Tag08KS.isIso_unit_app_iff_of_isClosedImmersion i A).mpr
      (annihilates_of_annihilates_affineOpens i hA)
  exact ⟨(Scheme.Modules.pullback i).obj A, isCoherent_pullback i A,
    ⟨(asIso ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app A)).symm⟩⟩

/-! ### The category and the equivalence -/

/-- The coherent `𝒪_X`-modules annihilated by the kernel ideal of the closed immersion `i`.
This is the category in the statement of Tag 087T. -/
abbrev CoherentAnnihilatedModules : Type _ :=
  ObjectProperty.FullSubcategory (C := X.Modules)
    (fun M => M.IsCoherent ∧ AnnihilatedByKer i M)

/-- The coherent `𝒪_Z`-modules, at the `SheafOfModules.IsCoherent` spelling of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherentFinitePresentation.lean`. -/
abbrev CoherentModulesOn (Z : Scheme.{u}) : Type _ :=
  ObjectProperty.FullSubcategory (C := Z.Modules) (fun M => M.IsCoherent)

variable [AlgebraicGeometry.IsClosedImmersion i] [IsLocallyNoetherian X] [IsLocallyNoetherian Z]

/-- **Direct image as a functor into the annihilated coherent modules.** Its composite with the
inclusion is `ι ⋙ i_*` on the nose, by `ObjectProperty.liftCompιIso`. -/
def coherentPushforward : CoherentModulesOn Z ⥤ CoherentAnnihilatedModules i :=
  ObjectProperty.lift _
    (ObjectProperty.ι (fun M : Z.Modules => M.IsCoherent) ⋙ Scheme.Modules.pushforward i)
    (fun G => by
      have hG : G.obj.IsCoherent := G.property
      have hGq : G.obj.IsQuasicoherent := isQuasicoherent_of_isCoherent G.obj
      exact ⟨Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
          i G.obj,
        annihilatedByKer_pushforward i G.obj⟩)

instance : (coherentPushforward i).Faithful :=
  have : (ObjectProperty.ι (fun M : Z.Modules => M.IsCoherent) ⋙
      Scheme.Modules.pushforward i).Faithful := inferInstance
  Functor.Faithful.of_comp_iso (G := ObjectProperty.ι _)
    (ObjectProperty.liftCompιIso _ _ _)

instance : (coherentPushforward i).Full :=
  have : (coherentPushforward i ⋙ ObjectProperty.ι _).Full :=
    Functor.Full.of_iso (ObjectProperty.liftCompιIso _ _ _).symm
  Functor.Full.of_comp_faithful (coherentPushforward i) (ObjectProperty.ι _)

instance : (coherentPushforward i).EssSurj where
  mem_essImage A := by
    have : A.obj.IsCoherent := A.property.1
    obtain ⟨G, hG, ⟨e⟩⟩ := exists_isCoherent_pushforward_iso i A.obj A.property.2
    exact ⟨⟨G, hG⟩, ⟨(ObjectProperty.fullyFaithfulι _).preimageIso e⟩⟩

instance : (coherentPushforward i).IsEquivalence where

/-- **[Stacks, Tag 087T].** Direct image along a closed immersion of locally Noetherian schemes
is an equivalence from the coherent modules on the source onto the coherent modules on the
target annihilated by the defining ideal, and the equivalence is the one induced by direct
image.

The second component of the pair is `ObjectProperty.liftCompιIso`, which is `Iso.refl`: the
functor was built as the lift of `ι ⋙ i_*`, so no identification is needed. -/
@[stacks 087T]
def coherentPushforwardEquivalence :
    Σ e : CoherentModulesOn Z ≌ CoherentAnnihilatedModules i,
      e.functor ⋙ ObjectProperty.ι
          (fun M : X.Modules => M.IsCoherent ∧ AnnihilatedByKer i M) ≅
        ObjectProperty.ι (fun M : Z.Modules => M.IsCoherent) ⋙ Scheme.Modules.pushforward i :=
  ⟨(coherentPushforward i).asEquivalence, ObjectProperty.liftCompιIso _ _ _⟩

end Stacks.AlgebraicGeometry.Tag087TCoherentImage

end

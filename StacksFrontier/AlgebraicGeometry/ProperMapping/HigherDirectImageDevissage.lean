module

public import StacksFrontier.AlgebraicGeometry.ProperMapping
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.DevissageFiltration
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.SchemeRestriction
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.Locality
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The long exact sequence of higher direct images, and the dévissage of 02O5 in all degrees

For a morphism of schemes `f : X ⟶ S`, the higher direct images `R ᵖ f_*` form a cohomological
δ-functor ([Stacks, Tag 010Q]), and the property "every `R ᵖ f_* F`, `p ≥ 0`, is coherent" of a
module `F` on `X` is a two-out-of-three property on short exact sequences. Through the dévissage
of [Stacks, Tag 01YG], coherence of all higher direct images of a coherent module
([Stacks, Tag 02O5]) therefore follows from two inputs:

* the existence of a dévissage filtration, [Stacks, Tag 01YF]; and
* coherence of every `R ᵖ f_* i_* I` for a quasi-coherent ideal `I ⊆ 𝒪_Z` on an integral closed
  subscheme `i : Z ⟶ X`.

## Main definitions

* `Stacks.AlgebraicGeometry.HigherDirectImageDevissage.higherDirectImageDeltaFunctor`: the
  cohomological δ-functor of the higher direct images along a morphism of schemes — the long
  exact sequence of higher direct images.
* `Stacks.AlgebraicGeometry.HigherDirectImageDevissage.CoherentHigherDirectImages`: the
  property "`R ᵖ f_* F` is coherent for every `p ≥ 0`".

## Main results

* `isCoherent_of_exact₄`: the five term sandwich for coherence — the middle term of an exact
  `A₀ ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄` with the other four coherent is coherent. This is
  [Stacks, Tag 02MO] (2) for the weak Serre subcategory of coherent modules, which is
  [Stacks, Tag 01BY] (5).
* `coherentHigherDirectImages_X₂_of_shortExact`, `coherentHigherDirectImages_X₃_of_shortExact`,
  `coherentHigherDirectImages_X₁_of_shortExact`: **two out of three implies the third** for
  `CoherentHigherDirectImages` on a short exact sequence, with no hypothesis on `f`.
* `coherentHigherDirectImages_of_isAffineOpen_restrict`: for `S` locally Noetherian,
  `CoherentHigherDirectImages` is local on `S`.
* `coherentHigherDirectImages_of_forall_hasIdealFiltration` and
  `isCoherent_higherDirectImage_of_forall_hasIdealFiltration`: every higher direct image of a
  coherent module is coherent, given dévissage filtrations ([Stacks, Tag 01YF]) and the
  integral-ideal base case.

## Implementation notes

**The sandwich is stated over a ringed space.** The instance
`Stacks.SheafOfModules.coherentModules_isWeakSerreClass` is an
`ObjectProperty (SheafOfModules.{u} R)`, and instance search does **not** find it at
`X.Modules`: `AlgebraicGeometry.Scheme.Modules` is a plain `def` with its own `Category` and
`Abelian` instances, so the class `IsWeakSerreClass (fun M : X.Modules => _)` is not syntactically
an instance of it. Stating `isCoherent_of_exact₄` over `SheafOfModules.{u} R` and *applying* it
to objects of `X.Modules` works, as for the closure lemmas of
`StacksFrontier/AlgebraicGeometry/ProperMapping.lean`.

**Every occurrence of the predicate is written `_root_.SheafOfModules.IsCoherent`.** Coherence is
declared twice as two distinct constants, and inside the `Stacks.` namespace both the bare name
and the dot notation resolve to `Stacks.SheafOfModules.IsCoherent`; the dévissage engine and the
closure theory used here are stated against the root constant, so leaving it unqualified would
silently state a different theorem. The crossing between the two is
`Stacks.AlgebraicGeometry.ProperMapping.stacksIsCoherent` and `isCoherent_of_stacks`.

**Degrees are natural numbers here, integers in the statement of the tag.** The δ-functor of
[Stacks, Tag 010Q] is `ℕ`-indexed, matching the source's `p ≥ 0`;
`isCoherent_higherDirectImage_of_forall_hasIdealFiltration` states the conclusion for every
`p : ℤ`, the negative degrees coming from
`Stacks.AlgebraicGeometry.ProperMapping.isCoherent_higherDirectImage_of_neg`, where `R ᵖ f_* F`
vanishes.

## References

* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 05TE](https://stacks.math.columbia.edu/tag/05TE)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open TopologicalSpace ZeroObject
open AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.AlgebraicGeometry.HigherDirectImageDevissage

/-! ### The five term sandwich for coherence -/

section Sandwich

variable {Y : Type u} [TopologicalSpace Y]
  {R : Sheaf (Opens.grothendieckTopology Y) RingCat.{u}}

/-- **[Stacks, Tag 02MO] (2) for coherent modules.** The middle term of a five term exact
sequence `A₀ ⟶ A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄` of modules on a ringed space whose other four terms are
coherent is coherent. -/
@[sga "6 I 3.4" "special case"]
theorem isCoherent_of_exact₄ {A₀ A₁ A₂ A₃ A₄ : SheafOfModules.{u} R}
    {f₀ : A₀ ⟶ A₁} {f₁ : A₁ ⟶ A₂} {f₂ : A₂ ⟶ A₃} {f₃ : A₃ ⟶ A₄}
    (w₀ : f₀ ≫ f₁ = 0) (w₁ : f₁ ≫ f₂ = 0) (w₂ : f₂ ≫ f₃ = 0)
    (e₀ : (ShortComplex.mk f₀ f₁ w₀).Exact) (e₁ : (ShortComplex.mk f₁ f₂ w₁).Exact)
    (e₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (h₀ : _root_.SheafOfModules.IsCoherent A₀) (h₁ : _root_.SheafOfModules.IsCoherent A₁)
    (h₃ : _root_.SheafOfModules.IsCoherent A₃) (h₄ : _root_.SheafOfModules.IsCoherent A₄) :
    _root_.SheafOfModules.IsCoherent A₂ :=
  ProperMapping.isCoherent_of_stacks
    (ObjectProperty.prop_mid_of_exact₄
      (P := fun M : SheafOfModules.{u} R => Stacks.SheafOfModules.IsCoherent M)
      (fun T hT a b c d => ObjectProperty.prop_obj₂_of_exact _ T hT a b c d)
      w₀ w₁ w₂ e₀ e₁ e₂
      (ProperMapping.stacksIsCoherent h₀) (ProperMapping.stacksIsCoherent h₁)
      (ProperMapping.stacksIsCoherent h₃) (ProperMapping.stacksIsCoherent h₄))

/-- **The sandwich with a monomorphism on the left.** If `A₁ ⟶ A₂` is a monomorphism and
`A₁ ⟶ A₂ ⟶ A₃ ⟶ A₄` is exact with `A₁`, `A₃` and `A₄` coherent, then `A₂` is coherent. -/
theorem isCoherent_of_mono_of_exact₃ {A₁ A₂ A₃ A₄ : SheafOfModules.{u} R}
    {f₁ : A₁ ⟶ A₂} {f₂ : A₂ ⟶ A₃} {f₃ : A₃ ⟶ A₄} (hf₁ : Mono f₁)
    (w₁ : f₁ ≫ f₂ = 0) (w₂ : f₂ ≫ f₃ = 0)
    (e₁ : (ShortComplex.mk f₁ f₂ w₁).Exact) (e₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (h₁ : _root_.SheafOfModules.IsCoherent A₁) (h₃ : _root_.SheafOfModules.IsCoherent A₃)
    (h₄ : _root_.SheafOfModules.IsCoherent A₄) :
    _root_.SheafOfModules.IsCoherent A₂ :=
  isCoherent_of_exact₄ (f₀ := (0 : (0 : SheafOfModules.{u} R) ⟶ A₁)) zero_comp w₁ w₂
    ((ShortComplex.exact_iff_mono _ rfl).2 hf₁) e₁ e₂
    (CoherentDevissage.isCoherent_of_isZero (isZero_zero _)) h₁ h₃ h₄

/-- **The sandwich as a kernel.** If `A₂ ⟶ A₃` is a monomorphism and `A₂ ⟶ A₃ ⟶ A₄` is exact with
`A₃` and `A₄` coherent, then `A₂` is coherent: it is a kernel of a morphism of coherent modules. -/
theorem isCoherent_of_mono_of_exact₂ {A₂ A₃ A₄ : SheafOfModules.{u} R}
    {f₂ : A₂ ⟶ A₃} {f₃ : A₃ ⟶ A₄} (hf₂ : Mono f₂) (w₂ : f₂ ≫ f₃ = 0)
    (e₂ : (ShortComplex.mk f₂ f₃ w₂).Exact)
    (h₃ : _root_.SheafOfModules.IsCoherent A₃) (h₄ : _root_.SheafOfModules.IsCoherent A₄) :
    _root_.SheafOfModules.IsCoherent A₂ :=
  isCoherent_of_mono_of_exact₃ (f₁ := (0 : (0 : SheafOfModules.{u} R) ⟶ A₂))
    ((isZero_zero _).mono _) zero_comp w₂
    ((ShortComplex.exact_iff_mono _ rfl).2 hf₂) e₂
    (CoherentDevissage.isCoherent_of_isZero (isZero_zero _)) h₃ h₄

end Sandwich

/-! ### The long exact sequence of higher direct images -/

section LongExactSequence

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The cohomological δ-functor of the higher direct images**, [Stacks, Tag 010Q], for a
morphism of schemes `f : X ⟶ S`. Its degree-`p` component is `R ᵖ f_*` and its fields are the
long exact sequence

  `0 ⟶ f_* F₁ ⟶ f_* F₂ ⟶ f_* F₃ ⟶ R ¹f_* F₁ ⟶ R ¹f_* F₂ ⟶ ⋯`

of a short exact sequence `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` of modules on `X`, together with naturality of
the connecting morphisms.

It is `Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor` ([Stacks, Tag 05TE]) of
`Scheme.Modules.pushforward f`, with the connecting morphism
`Stacks.DerivedIndexing.canonicalδ`. -/
def higherDirectImageDeltaFunctor : DeltaFunctor X.Modules S.Modules :=
  Stacks.DerivedIndexing.rightDerivedPlusDeltaFunctor (Scheme.Modules.pushforward f)
    (Stacks.DerivedIndexing.derivedDeltaFunctorStructure (Scheme.Modules.pushforward f))
    (Stacks.DerivedIndexing.canonicalδ (Scheme.Modules.pushforward f)) (fun _ _ => rfl)

/-- The degree-`p` component of `higherDirectImageDeltaFunctor` is `R ᵖ f_*`, on the nose. -/
theorem higherDirectImageDeltaFunctor_functor (p : ℕ) :
    (higherDirectImageDeltaFunctor f).functor p =
      (Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ) :=
  rfl

/-- **The connecting morphism `R ᵖ f_* F₃ ⟶ R ᵖ⁺¹ f_* F₁`** of a short exact sequence of modules
on `X`. -/
def higherDirectImageδ {T : ShortComplex X.Modules} (hT : T.ShortExact) (p : ℕ) :
    ((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj T.X₃ ⟶
      ((Scheme.Modules.pushforward f).rightDerivedPlus ((p + 1 : ℕ) : ℤ)).obj T.X₁ :=
  (higherDirectImageDeltaFunctor f).δ hT p

end LongExactSequence

/-! ### Coherence of all the higher direct images, and two out of three -/

section TwoOutOfThree

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- Every higher direct image `R ᵖ f_* F`, `p ≥ 0`, is coherent. The negative degrees are omitted
because `R ᵖ f_* F` vanishes there for every `f` and every `F`, by
`Stacks.AlgebraicGeometry.ProperMapping.isCoherent_higherDirectImage_of_neg`. -/
def CoherentHigherDirectImages (F : X.Modules) : Prop :=
  ∀ p : ℕ, _root_.SheafOfModules.IsCoherent
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F)

/-- A zero module has property `CoherentHigherDirectImages`. -/
theorem coherentHigherDirectImages_of_isZero {F : X.Modules} (hF : IsZero F) :
    CoherentHigherDirectImages f F := fun p =>
  have := (higherDirectImageDeltaFunctor f).additive p
  CoherentDevissage.isCoherent_of_isZero (R := S.ringCatSheaf)
    (((higherDirectImageDeltaFunctor f).functor p).map_isZero hF)

/-- The terminal module has property `CoherentHigherDirectImages`. -/
theorem coherentHigherDirectImages_terminal :
    CoherentHigherDirectImages f (⊤_ X.Modules) :=
  coherentHigherDirectImages_of_isZero f CoherentDevissage.isZero_terminal

/-- **Two out of three, the middle term.** If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is a short exact sequence of
modules on `X` and all the higher direct images of `F₁` and of `F₃` are coherent, then so are all
the higher direct images of `F₂`. -/
theorem coherentHigherDirectImages_X₂_of_shortExact {T : ShortComplex X.Modules}
    (hT : T.ShortExact) (h₁ : CoherentHigherDirectImages f T.X₁)
    (h₃ : CoherentHigherDirectImages f T.X₃) :
    CoherentHigherDirectImages f T.X₂ := by
  set D := higherDirectImageDeltaFunctor f
  intro p
  match p with
  | 0 =>
    exact isCoherent_of_mono_of_exact₃ (f₃ := D.δ hT 0) (D.mono_map_f hT)
      (D.map_f_comp_map_g 0) (D.map_g_δ hT 0) (D.exact_map hT 0) (D.exact_δ₁ hT 0)
      (h₁ 0) (h₃ 0) (h₁ 1)
  | (q + 1) =>
    exact isCoherent_of_exact₄ (f₀ := D.δ hT q) (D.δ_map_f hT q)
      (D.map_f_comp_map_g (q + 1)) (D.map_g_δ hT (q + 1))
      (D.exact_δ₂ hT q) (D.exact_map hT (q + 1)) (D.exact_δ₁ hT (q + 1))
      (h₃ q) (h₁ (q + 1)) (h₃ (q + 1)) (h₁ (q + 2))

/-- **Two out of three, the third term.** If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact and all the
higher direct images of `F₁` and of `F₂` are coherent, then so are all those of `F₃`. -/
theorem coherentHigherDirectImages_X₃_of_shortExact {T : ShortComplex X.Modules}
    (hT : T.ShortExact) (h₁ : CoherentHigherDirectImages f T.X₁)
    (h₂ : CoherentHigherDirectImages f T.X₂) :
    CoherentHigherDirectImages f T.X₃ := by
  set D := higherDirectImageDeltaFunctor f
  intro p
  exact isCoherent_of_exact₄ (f₀ := (D.functor p).map T.f)
    (D.map_f_comp_map_g p) (D.map_g_δ hT p) (D.δ_map_f hT p)
    (D.exact_map hT p) (D.exact_δ₁ hT p) (D.exact_δ₂ hT p)
    (h₁ p) (h₂ p) (h₁ (p + 1)) (h₂ (p + 1))

/-- **Two out of three, the first term.** If `0 ⟶ F₁ ⟶ F₂ ⟶ F₃ ⟶ 0` is short exact and all the
higher direct images of `F₂` and of `F₃` are coherent, then so are all those of `F₁`. -/
theorem coherentHigherDirectImages_X₁_of_shortExact {T : ShortComplex X.Modules}
    (hT : T.ShortExact) (h₂ : CoherentHigherDirectImages f T.X₂)
    (h₃ : CoherentHigherDirectImages f T.X₃) :
    CoherentHigherDirectImages f T.X₁ := by
  set D := higherDirectImageDeltaFunctor f
  intro p
  match p with
  | 0 =>
    exact isCoherent_of_mono_of_exact₂ (f₂ := (D.functor 0).map T.f)
      (f₃ := (D.functor 0).map T.g) (D.mono_map_f hT) (D.map_f_comp_map_g 0)
      (D.exact_map hT 0) (h₂ 0) (h₃ 0)
  | (q + 1) =>
    exact isCoherent_of_exact₄ (f₀ := (D.functor q).map T.g)
      (D.map_g_δ hT q) (D.δ_map_f hT q) (D.map_f_comp_map_g (q + 1))
      (D.exact_δ₁ hT q) (D.exact_δ₂ hT q) (D.exact_map hT (q + 1))
      (h₂ q) (h₃ q) (h₂ (q + 1)) (h₃ (q + 1))

/-- **Coherence of the higher direct images is local on the target.** If `S` is locally
Noetherian and, for every affine open `V ⊆ S`, every higher direct image of `F|_{f⁻¹V}` along the
restricted morphism `f ∣_ V` is coherent, then every higher direct image of `F` along `f` is
coherent. -/
theorem coherentHigherDirectImages_of_isAffineOpen_restrict [IsLocallyNoetherian S]
    (F : X.Modules)
    (h : ∀ V : S.Opens, IsAffineOpen V →
      CoherentHigherDirectImages (f ∣_ V)
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)) :
    CoherentHigherDirectImages f F := by
  intro p
  refine Stacks.FundamentalGroup.ExtendedEtaleFold.isCoherent_of_isAffineOpen_restrict _
    fun W hW => ?_
  have := h W hW p
  exact CoherentDevissage.isCoherent_of_iso
    (SchemeHigherDirectImage.rightDerivedPlusRestrictObjIso f W p F).symm

end TwoOutOfThree

/-! ### [Stacks, Tag 02O5] in all degrees, reduced to 01YF and one base case -/

section Reduction

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 02O5] in all degrees, reduced to [Stacks, Tag 01YF] and one base case.**
Suppose

* `hfil`: every coherent module on `X` carries a dévissage filtration — this is
  [Stacks, Tag 01YF]; and
* `hideal`: every higher direct image `R ᵖ f_* i_* I` is coherent, for every quasi-coherent ideal
  `I ⊆ 𝒪_Z` on every integral closed subscheme `i : Z ⟶ X`.

Then every higher direct image `R ᵖ f_* F`, `p ≥ 0`, is coherent, for every coherent `F`. -/
theorem coherentHigherDirectImages_of_forall_hasIdealFiltration
    (hfil : ∀ G : X.Modules, _root_.SheafOfModules.IsCoherent G →
      CoherentDevissage.HasIdealFiltration G)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [AlgebraicGeometry.IsIntegral Z] (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      CoherentHigherDirectImages f ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) :
    CoherentHigherDirectImages f F :=
  CoherentDevissage.property_of_forall_hasIdealFiltration (CoherentHigherDirectImages f) hfil
    (coherentHigherDirectImages_terminal f)
    (fun _ hT _ _ _ hP₁ hP₃ => coherentHigherDirectImages_X₂_of_shortExact f hT hP₁ hP₃)
    hideal F hF

/-- **[Stacks, Tag 02O5] for every integer degree, reduced to [Stacks, Tag 01YF] and one base
case.** The same statement as `coherentHigherDirectImages_of_forall_hasIdealFiltration` with the
degree ranging over `ℤ` as in the source's `R ⁱ f_* F`: in negative degrees the higher direct
image vanishes, so nothing is assumed there. -/
theorem isCoherent_higherDirectImage_of_forall_hasIdealFiltration
    (hfil : ∀ G : X.Modules, _root_.SheafOfModules.IsCoherent G →
      CoherentDevissage.HasIdealFiltration G)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
      [AlgebraicGeometry.IsIntegral Z] (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      CoherentHigherDirectImages f ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (F : X.Modules) (hF : _root_.SheafOfModules.IsCoherent F) (p : ℤ) :
    _root_.SheafOfModules.IsCoherent
      (((Scheme.Modules.pushforward f).rightDerivedPlus p).obj F) := by
  rcases lt_or_ge p 0 with hp | hp
  · exact ProperMapping.isCoherent_higherDirectImage_of_neg f F p hp
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le hp
    exact coherentHigherDirectImages_of_forall_hasIdealFiltration f hfil hideal F hF q

end Reduction

end Stacks.AlgebraicGeometry.HigherDirectImageDevissage

end

end

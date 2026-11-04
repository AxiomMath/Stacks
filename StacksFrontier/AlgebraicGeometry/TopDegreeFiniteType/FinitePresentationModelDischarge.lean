module

public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.AffineBaseChangeProjection
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.FinitePresentationAffineBase
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.FinitePresentationNoetherianModel
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Unconditional
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tag 0EX5: the Noetherian model discharged

The statement of [Stacks, Tag 0EX5] in
`StacksFrontier/AlgebraicGeometry/TopDegreeFiniteType/FinitePresentationAffineBase.lean` carries a
hypothesis `hmodel` with two halves: that the affine situation of the tag has a locally
Noetherian model, and that `R ᵈ f_* F` is the pullback of its value at that model. Both halves
are content of the tag's own proof rather than hypotheses of the tag, so neither may stand as a
binder.

This file removes the first half from the binder. The model is
`Stacks.AlgebraicGeometry.NoetherianModel.exists_noetherianModel`, the absolute Noetherian
approximation of paragraph four of the proof of [Stacks, Tag 0EX4]; the vanishing above the
fibre dimension that the base-change step consumes is
`…TopDegreeFiniteType.isZero_rightDerivedPlus_pushforward_of_forall_topologicalKrullDim_fiber_le`,
which holds with no hypothesis. What is left is the base-change identification at the
Noetherian stage, and nothing else.

## Main results

* `…TopDegreeFiniteType.exists_pullback_rightDerived_iso_of_baseChangeIso`: **`hmodel` from the
  base-change isomorphism alone.** Granted that `R ᵈ f_* F` commutes with base change along an
  affine-to-Noetherian-affine cartesian square — clause (c) of [Stacks, Tag 0EX3] at the
  stage — the whole of `hmodel` follows. The Noetherian model itself is no longer assumed.
* `…TopDegreeFiniteType.isFinitePresentation_rightDerived_of_topDegreeBaseChange`:
  **[Stacks, Tag 0EX5] over an arbitrary base with the model and the vanishing both
  discharged**, carrying only the finite-presentation conclusion at the Noetherian stage. This
  is strictly weaker than `hmodel`: no isomorphism is asked for, only that the top higher direct
  image of the base change of a finitely presented module over an affine Noetherian stage be of
  finite presentation.
* `…TopDegreeFiniteType.isFinitePresentation_rightDerived_of_finitePresentation`:
  **[Stacks, Tag 0EX5] at the tag's own hypotheses, with nothing carried.** The last input is
  discharged by
  `…AffineBaseChangeProjection.isFinitePresentation_rightDerived_pullback_of_noetherianModel`,
  so `R ᵈ f_* F` is of finite presentation for `f` proper and of finite presentation with fibres
  of dimension at most `d` and `F` of finite presentation — no Noetherian hypothesis on `Y`, no
  model assumed, no base change assumed. This statement carries the attribute.

## Implementation notes

**Why two statements and not one.** The two consumers of the Noetherian model want different
things from the stage. `hmodel`, as the tag's statement is currently phrased, wants an
isomorphism `u^* R ᵈ (g₀)_* G₀ ≅ R ᵈ g_* G`; the proof only ever uses the finite presentation
that isomorphism transports. The second statement below is therefore the one the tag should
rest on, and the first is recorded because it is what discharges the binder as it stands.

**Which statement carries `@[stacks 0EX5]`.** The first two still carry a hypothesis that is
content of the tag's proof — the base-change isomorphism in the first, its finite-presentation
shadow in the second — so neither is the tag. The third carries nothing and is the tag, so the
attribute is on it. The conditional pair is kept because each isolates one input of the proof,
which is what makes the third one's three lines readable.

**The `hmodel`-carrying statement in `FinitePresentationAffineBase.lean` is now redundant.**
`…isFinitePresentation_rightDerived_of_moduleFinite_cohomology_of_noetherianModel` proves the
same conclusion from a hypothesis that is the tag's own content. It could not be stated
unconditionally there: the discharge of its last input lives in
`AffineBaseChangeProjection.lean`, which imports `FinitePresentationAffineBase.lean`, so the
unconditional statement has to sit downstream of both. It is left in place, unchanged, as the
shape the limit argument asks of its stage, with the registration it already has, which names
`hmodel` and so records the conditional form only. The statement below, which carries no
hypothesis beyond the tag's own, has its own `@[stacks 0EX5]` registration.

**The fibre bound travels to the stage.** `exists_noetherianModel` produces a model whose fibres
satisfy the same bound, which is what lets the unconditional vanishing be applied over the stage
rather than assumed there; that is the only reason the vanishing can be discharged here and not
in `FinitePresentationUnconditional.lean`, which does not import
`…TopDegreeFiniteType.Unconditional`.

## References

* [Stacks Project, Tag 0EX5](https://stacks.math.columbia.edu/tag/0EX5)
* [Stacks Project, Tag 0EX4](https://stacks.math.columbia.edu/tag/0EX4)
* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 0E7D](https://stacks.math.columbia.edu/tag/0E7D)
-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeFiniteType

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The `hmodel` hypothesis of [Stacks, Tag 0EX5], from the base-change isomorphism alone.**

`hbciso` is clause (c) of [Stacks, Tag 0EX3] read at the top degree over a cartesian square
```
X' --p--> X₀
|g'       |g₀
Y' --v--> S₀
```
with `S₀` affine Noetherian, `g₀` proper with fibres of dimension at most `d`, and `Y'` affine:
the canonical comparison `v^* R ᵈ (g₀)_* G₀ ≅ R ᵈ (g')_* (p^* G₀)` is an isomorphism.

Granted that, the existential statement `hmodel` asks for holds: the model is
`…NoetherianModel.exists_noetherianModel` — absolute Noetherian approximation of the base
together with descent of the proper morphism of finite presentation, of its fibre bound and of
the module — and the isomorphism it produces between `G` and the pullback of `G₀` is carried
through `R ᵈ g_*` and composed with `hbciso`.

So the existence half of `hmodel` is not a hypothesis of anything: only the base-change half
is. -/
theorem exists_pullback_rightDerived_iso_of_baseChangeIso (d : ℕ)
    (hbciso : ∀ (X₀ S₀ X' Y' : Scheme.{u}) (g₀ : X₀ ⟶ S₀), IsProper g₀ → IsAffine S₀ →
      IsNoetherian S₀ → (∀ s : S₀, topologicalKrullDim (g₀.fiber s) ≤ (d : WithBot ℕ∞)) →
      ∀ G₀ : X₀.Modules, G₀.IsFinitePresentation →
      ∀ (g' : X' ⟶ Y') (p : X' ⟶ X₀) (v : Y' ⟶ S₀), IsAffine Y' → IsPullback p g' g₀ v →
        Nonempty ((Scheme.Modules.pullback v).obj
            (((Scheme.Modules.pushforward g₀).rightDerived d).obj G₀) ≅
          ((Scheme.Modules.pushforward g').rightDerived d).obj
            ((Scheme.Modules.pullback p).obj G₀))) :
    ∀ (X' Y' : Scheme.{u}) (g : X' ⟶ Y'), IsProper g →
      AlgebraicGeometry.FinitePresentation g → IsAffine Y' →
      (∀ s : Y', topologicalKrullDim (g.fiber s) ≤ (d : WithBot ℕ∞)) →
        ∀ G : X'.Modules, G.IsFinitePresentation →
          ∃ (X₀ S₀ : Scheme.{u}) (g₀ : X₀ ⟶ S₀) (_ : IsProper g₀)
            (_ : IsLocallyNoetherian S₀) (G₀ : X₀.Modules) (_ : G₀.IsFinitePresentation)
            (u : Y' ⟶ S₀),
            Nonempty ((Scheme.Modules.pullback u).obj
                (((Scheme.Modules.pushforward g₀).rightDerived d).obj G₀) ≅
              ((Scheme.Modules.pushforward g).rightDerived d).obj G) := by
  intro X' Y' g hg hgfp hY' hgdim G hG
  have := hg
  have := hY'
  have := hG
  obtain ⟨X₀, S₀, g₀, hpr, _hfp₀, haff₀, hnoeth₀, hdim₀, G₀, hG₀, u, p, hsq, ⟨eG⟩⟩ :=
    Stacks.AlgebraicGeometry.NoetherianModel.exists_noetherianModel g hgfp d hgdim G
  obtain ⟨ebc⟩ := hbciso X₀ S₀ X' Y' g₀ hpr haff₀ hnoeth₀ hdim₀ G₀ hG₀ g p u inferInstance hsq
  exact ⟨X₀, S₀, g₀, hpr, hnoeth₀.toIsLocallyNoetherian, G₀, hG₀, u,
    ⟨ebc ≪≫ (((Scheme.Modules.pushforward g).rightDerived d).mapIso eG).symm⟩⟩

/-- **[Stacks, Tag 0EX5] over an arbitrary base, with the Noetherian model and the vanishing
above the fibre dimension both discharged.**

For `f : X ⟶ Y` proper and of finite presentation all of whose fibres have dimension at most
`d`, and `F` an `𝒪_X`-module of finite presentation, the `𝒪_Y`-module `R ᵈ f_* F` is of finite
presentation — granted only `hbc`, finite presentation of `R ᵈ (g')_* (p^* G₀)` over a cartesian
square of the shape the Noetherian model produces.

Three of the four steps of the source's proof are discharged:

* the conclusion is local on `Y`, so `Y` may be taken affine —
  `…isFinitePresentation_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase`;
* over an affine base the situation descends to an affine **Noetherian** stage, with the proper
  morphism of finite presentation, the fibre bound and the module all descending with it —
  `…NoetherianModel.exists_noetherianModel`;
* over that stage the higher direct images vanish above `d` —
  `…isZero_rightDerivedPlus_pushforward_of_forall_topologicalKrullDim_fiber_le`, which holds
  with no hypothesis at all and in particular needs nothing Noetherian.

What `hbc` still carries is the fourth step, the top-degree base change of [Stacks, Tag 0EX3]
along the model. No `@[stacks 0EX5]` attribute while it does.

This hypothesis is strictly weaker than the `hmodel` of
`…isFinitePresentation_rightDerived_of_moduleFinite_cohomology_of_noetherianModel`: it asks for
no isomorphism and nothing about the existence of a model, only for the finiteness conclusion at
a stage that is handed to it. -/
theorem isFinitePresentation_rightDerived_of_topDegreeBaseChange
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (hfp : AlgebraicGeometry.FinitePresentation f)
    (d : ℕ) (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsFinitePresentation]
    (hbc : ∀ (X₀ S₀ X' Y' : Scheme.{u}) (g₀ : X₀ ⟶ S₀), IsProper g₀ → IsAffine S₀ →
      IsNoetherian S₀ → ∀ G₀ : X₀.Modules, G₀.IsFinitePresentation →
      (∀ j : ℤ, (d : ℤ) < j → ∀ G' : X₀.Modules, G'.IsQuasicoherent →
        IsZero (((Scheme.Modules.pushforward g₀).rightDerivedPlus j).obj G')) →
      ∀ (g' : X' ⟶ Y') (p : X' ⟶ X₀) (v : Y' ⟶ S₀), IsAffine Y' → IsPullback p g' g₀ v →
        (((Scheme.Modules.pushforward g').rightDerived d).obj
          ((Scheme.Modules.pullback p).obj G₀)).IsFinitePresentation) :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFinitePresentation := by
  refine isFinitePresentation_rightDerived_of_forall_topologicalKrullDim_fiber_le_of_affineBase
    f hfp d hdim F fun X' Y' g hg hgfp hY' hgdim G hG => ?_
  have := hg
  have := hY'
  have := hG
  obtain ⟨X₀, S₀, g₀, hpr, _hfp₀, haff₀, hnoeth₀, hdim₀, G₀, hG₀, u, p, hsq, ⟨eG⟩⟩ :=
    Stacks.AlgebraicGeometry.NoetherianModel.exists_noetherianModel g hgfp d hgdim G
  have hres := hbc X₀ S₀ X' Y' g₀ hpr haff₀ hnoeth₀ G₀ hG₀
    (isZero_rightDerivedPlus_pushforward_of_forall_topologicalKrullDim_fiber_le d
      X₀ S₀ g₀ hpr haff₀ hnoeth₀ hdim₀) g p u inferInstance hsq
  exact (_root_.SheafOfModules.isFinitePresentation.{u, u, u} Y'.ringCatSheaf).prop_of_iso
    (((Scheme.Modules.pushforward g).rightDerived d).mapIso eG).symm hres

/-! ### The tag -/

open Stacks.AlgebraicGeometry.AffineBaseChangeProjection in
/-- **[Stacks, Tag 0EX5].** Let `f : X ⟶ Y` be proper and of finite presentation with every
fibre of dimension at most `d`, and let `F` be an `𝒪_X`-module of finite presentation. Then the
`𝒪_Y`-module `R ᵈ f_* F` is of finite presentation.

No hypothesis is carried: `Y` is an arbitrary scheme, in particular not assumed locally
Noetherian, and nothing about Noetherian models or about base change is assumed.

The proof is the source's, which is the proof of [Stacks, Tag 0EX4] with the third paragraph
skipped, and it is now assembled from three pieces that are each unconditional:

* the conclusion is local on `Y`, so `Y` may be taken affine, and over an affine base the
  situation descends to an affine **Noetherian** stage together with the fibre bound and the
  module, over which the higher direct images vanish above `d` — this is
  `isFinitePresentation_rightDerived_of_topDegreeBaseChange` above;
* over that stage the top higher direct image of the base change is of finite presentation —
  `…AffineBaseChangeProjection.isFinitePresentation_rightDerived_pullback_of_noetherianModel`,
  the Eilenberg–Watts argument of [Stacks, Tag 0EX3] (b) applied at `Γ(Y, ⊤)`.

The conclusion is read as the statement about the `𝒪_Y`-module `R ᵈ f_* F`; the source prints
`𝒪_X`, which is a typo, the higher direct image being a sheaf on `Y`. -/
@[stacks 0EX5 "conclusion read as the 𝒪_Y-module R ᵈ f_* F, the source's 𝒪_X being a typo",
  ega "III 2.4.1" "Clause (i), special case"]
theorem isFinitePresentation_rightDerived_of_finitePresentation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (hfp : AlgebraicGeometry.FinitePresentation f)
    (d : ℕ) (hdim : ∀ y : Y, topologicalKrullDim (f.fiber y) ≤ (d : WithBot ℕ∞))
    (F : X.Modules) [F.IsFinitePresentation] :
    (((Scheme.Modules.pushforward f).rightDerived d).obj F).IsFinitePresentation := by
  refine isFinitePresentation_rightDerived_of_topDegreeBaseChange f hfp d hdim F
    fun X₀ S₀ X' Y' g₀ hpr haff₀ hnoeth₀ G₀ hG₀ hvan g p v hY' hsq => ?_
  have := hpr
  have := haff₀
  have := hnoeth₀
  have := hG₀
  have := hY'
  exact isFinitePresentation_rightDerived_pullback_of_noetherianModel g₀ d hvan G₀ hsq

end Stacks.AlgebraicGeometry.TopDegreeFiniteType

end

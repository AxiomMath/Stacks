module

public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.Connected
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.ConnectedIrreducible

/-!
# Geometric connectedness and irreducibility of the zero scheme of an ample regular section

[Stacks, Tag 0FD9] concludes that the zero scheme `Z(s)` of a regular section of an ample
invertible module on a connected proper scheme over a field, whose local rings at closed points
have depth at least `2`, is connected. The Bertini induction of [Stacks, Tag 0FH7] needs more
than that topological conclusion: it needs `Z(s)` to be *geometrically* connected, and — once
`Z(s)` is known to be smooth over the base field — irreducible.

Both upgrades are available from results in the library, and this module performs the two
compositions.
A connected scheme over a field with a rational point is geometrically connected
([Stacks, Tag 04KV]), and a connected scheme smooth over a field is irreducible
([Stacks, Tag 056S] and [Stacks, Tag 033M]).

## Main results

* `Stacks.AmpleSectionConnected.geometricallyConnected_zeroScheme_of_isAmple`: the zero scheme of
  [Stacks, Tag 0FD9] is geometrically connected over the base field once it carries a rational
  point.
* `Stacks.AmpleSectionConnected.irreducibleSpace_zeroScheme_of_isAmple`: the zero scheme of
  [Stacks, Tag 0FD9] is irreducible once it is quasi-compact and smooth over the base field.

## Implementation notes

The hypotheses of [Stacks, Tag 0FD9] are reproduced verbatim from
`Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_isAmple`, which supplies the
`ConnectedSpace` instance each conclusion consumes.

The structure morphism `g` of the zero scheme over `k` is taken as a hypothesis rather than
constructed from `f`: the closed immersion of the zero scheme into `X` composed with `f` is one
such morphism, but every statement here is about an arbitrary structure morphism, and the two
conclusions are each about that morphism — geometric connectedness is a property of a morphism,
not of a space.

No `@[stacks 0FD9]` attribute is attached. The source statement of that tag has no geometric
clause and no irreducibility clause: its hypothesis on `X` is plain connectedness and its
conclusion is plain connectedness of `Z(s)`, so the whole of the tag is already carried by
`Stacks.AmpleSectionConnected.connectedSpace_zeroScheme_of_isAmple`. The results here are
infrastructure for [Stacks, Tag 0FH7].

Irreducibility is taken through the quasi-compact form
`AlgebraicGeometry.irreducibleSpace_of_smooth_of_connectedSpace_of_compactSpace` rather than the
Noetherian form, because smoothness over the field already supplies local finite type and hence
local Noetherianness; only quasi-compactness has to be assumed.

## References

* [Stacks Project, Tag 0FD9](https://stacks.math.columbia.edu/tag/0FD9)
* [Stacks Project, Tag 0FH7](https://stacks.math.columbia.edu/tag/0FH7)
* [Stacks Project, Tag 04KV](https://stacks.math.columbia.edu/tag/04KV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.AmpleSectionConnected

variable (k : Type u) [Field k] {X : Scheme.{u}}
  (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
  [inst : AlgebraicGeometry.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L]

/-- **The zero scheme of [Stacks, Tag 0FD9] is geometrically connected once it has a rational
point.** Under the hypotheses of that tag — `X` proper and connected over the field `k`, `ℒ`
ample and invertible, `s` a regular section, and `depth(𝒪_{X,x}) ≥ 2` at every closed point — a
structure morphism `g` of `Z(s)` over `k` admitting a section is geometrically connected. -/
theorem geometricallyConnected_zeroScheme_of_isAmple
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) (s : L.sections)
    (hs : Mono (L.unitHomEquiv.symm s))
    (hdepth : ∀ x : X, IsClosed ({x} : Set X) → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    [ConnectedSpace X]
    (g : (zeroScheme X L (s.eval (op ⊤))).subscheme ⟶ Spec (.of k))
    (σ : Spec (.of k) ⟶ (zeroScheme X L (s.eval (op ⊤))).subscheme) (hσ : σ ≫ g = 𝟙 _) :
    GeometricallyConnected g :=
  have : ConnectedSpace (zeroScheme X L (s.eval (op ⊤))).subscheme :=
    connectedSpace_zeroScheme_of_isAmple k f L hL s hs hdepth
  geometricallyConnected_of_connectedSpace_of_section g σ hσ

/-- **The zero scheme of [Stacks, Tag 0FD9] is irreducible once it is quasi-compact and smooth
over the base field.** Under the hypotheses of that tag, a structure morphism `g` of `Z(s)` over
`k` which is smooth makes `Z(s)` irreducible. -/
theorem irreducibleSpace_zeroScheme_of_isAmple
    (f : X ⟶ Spec (.of k)) [IsProper f]
    (hL : AlgebraicGeometry.Scheme.Modules.IsAmple X L) (s : L.sections)
    (hs : Mono (L.unitHomEquiv.symm s))
    (hdepth : ∀ x : X, IsClosed ({x} : Set X) → (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    [ConnectedSpace X]
    (g : (zeroScheme X L (s.eval (op ⊤))).subscheme ⟶ Spec (.of k)) [Smooth g]
    [CompactSpace (zeroScheme X L (s.eval (op ⊤))).subscheme] :
    IrreducibleSpace (zeroScheme X L (s.eval (op ⊤))).subscheme :=
  have : ConnectedSpace (zeroScheme X L (s.eval (op ⊤))).subscheme :=
    connectedSpace_zeroScheme_of_isAmple k f L hL s hs hdepth
  irreducibleSpace_of_smooth_of_connectedSpace_of_compactSpace g

end Stacks.AmpleSectionConnected

end

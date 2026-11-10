module

public import StacksFrontier.AlgebraicGeometry.SectionExtension.AmpleConsumers
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 01VN with the quasi-compactness of the ambient scheme removed

`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/Basic.lean` proves the content of Stacks Tag
01VN with the projective bundle generalised: relative ampleness is inherited by an immersion over
the base. `StacksFrontier/AlgebraicGeometry/SectionExtension/AmpleConsumers.lean` discharges its
last premise, so `Stacks.SectionExtension.isRelativelyAmple_of_relativeTwistImmersion` is
unconditional. Its hypothesis
`Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f L` asks for an `S`-scheme `P`, an invertible
`𝒪_P`-module `M` with `Stacks.RelativeAmple.IsRelativelyAmple p M`, and an immersion `i : X ⟶ P`
over `S` with `L ≅ i^* M`.

**That hypothesis cannot be instantiated at the case Stacks Tag 01VM is stated in**, and the reason
is not the missing twist. `Stacks.RelativeAmple.IsRelativelyAmple p M` is by definition
`QuasiCompact p ∧ …`, so it forces the structure morphism of the ambient scheme to be
quasi-compact — `quasiCompact_of_hasRelativeTwistImmersion` below is that implication, stated so
that the point is machine-checked rather than asserted. For `P = 𝐏(E) = Proj_S(Sym(E))` with `E` an
arbitrary quasi-coherent `𝒪_S`-module this fails: already for `S = Spec R` and `E = 𝒪_S^{(ℕ)}` the
space `Proj R[x₀, x₁, …]` is not quasi-compact, since the homogeneous prime `(x₀, …, x_n)` is a
point of it outside `D₊(x₀) ∪ … ∪ D₊(x_n)` for every `n`. So a value of
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData` together with a proof that `𝒪(1)` is ample
on the affine charts does not suffice to specialise the library's theorem to Tag 01VN at the
generality of Tag 01VM;
the sentence "it specialises to Tag 01VN the moment `𝒪(1)` is built on `𝐏(E)` and known relatively
ample there", in the module documentation of `RelativeVeryAmple/Basic.lean`, is true only for an
`E` whose bundle is quasi-compact over `S`.

This file removes that obstruction, by observing which part of the ampleness of `M` the proof
actually consumes. `Stacks.AmpleLocallyClosed.isBasisNonvanishing_pullback` transports clause (3)
of Stacks Tag 01Q3 — the opens `X_s`, for `s` a global section of a positive tensor power, form a
basis for the topology — along a topological embedding, and that clause says nothing about
quasi-compactness. `Stacks.AmpleTheory.isAmple_of_isBasisAffineNonvanishing` then needs
quasi-compactness only of the *source*, which Tag 01VN already has from `QuasiCompact f`. So the
ampleness of `M` enters the argument exclusively through clause (3), and clause (3) is what the
hypothesis should ask for.

## Main definitions

* `Stacks.RelativeAmpleBasisRoute.HasRelativeBasisImmersion`: the hypothesis of Stacks Tag 01VN
  with relative ampleness of `M` weakened to clause (3) of Stacks Tag 01Q3 on the preimage of
  every affine open of the base. **No quasi-compactness of `P ⟶ S` is asked for.**

## Main results

* `Stacks.RelativeAmpleBasisRoute.isAmple_pullbackModule_of_isBasisNonvanishing`: **Stacks Tag
  0B3E with the ampleness of the target module replaced by clause (3) of Stacks Tag 01Q3.** If the
  `X_s` form a basis for the topology of `X`, `X'` is quasi-compact and `j : X' ⟶ X` is a
  topological embedding, then `j^* L` is ample on `X'` — and `L` need not be ample, nor `X`
  quasi-compact.
* `Stacks.RelativeAmpleBasisRoute.isRelativelyAmple_of_hasRelativeBasisImmersion`: **the content
  of Stacks Tag 01VN on the weakened hypothesis.**
* `Stacks.RelativeAmpleBasisRoute.hasRelativeBasisImmersion_of_hasRelativeTwistImmersion` and
  `isRelativelyAmple_of_relativeTwistImmersion`: the weakened hypothesis is implied by the
  twist-immersion one, so the theorem above subsumes
  `Stacks.SectionExtension.isRelativelyAmple_of_relativeTwistImmersion`.
* `Stacks.RelativeAmpleBasisRoute.quasiCompact_of_hasRelativeTwistImmersion`: the
  twist-immersion hypothesis forces `QuasiCompact p`, which is the obstruction described above.

## What is not done

**Stacks Tag 01VN's remaining input is a property of the twist, not the twist itself.** Tag 01VM
needs `𝒪_{𝐏(E)}(1)`, and that needs a value of
`Stacks.AlgebraicGeometry.RelativeProjTwists.TwistData`; one is produced from a quasi-coherent
graded algebra alone, with no further hypothesis, by
`Stacks.AlgebraicGeometry.GluedTwistAlgebra.twistDataOfGradedAlgebra`, so for `𝐏(E) =
Proj_S(Sym(E))` the twist is available.
What changes here is what must then be proved *about* that twist: not that it is ample relative to
`𝐏(E) ⟶ S` — which is false for a general quasi-coherent `E`, by the paragraph above — but that
its nonvanishing opens form a basis for the topology of each `p⁻¹(V)`, which is a local statement
and the one the charts can supply.

**No Stacks attribute is attached.** Tag 01VN's covering set is its own theorem, whose statement
mentions relative very ampleness and therefore the twist; nothing here states it. Tag 0B3E's
attribute already sits on `Stacks.Tag0B3E.isAmple_modulePullback` and Tag 01Q3's clauses are
registered on other declarations; `isAmple_pullbackModule_of_isBasisNonvanishing` is a
strengthening of the
first, not a restatement of it, so it earns neither.

## References

* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 01VM](https://stacks.math.columbia.edu/tag/01VM)
* [Stacks Project, Tag 01VH](https://stacks.math.columbia.edu/tag/01VH)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PX](https://stacks.math.columbia.edu/tag/01PX)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample

universe u

namespace Stacks.RelativeAmpleBasisRoute

/-! ### Stacks Tag 0B3E from clause (3) of Stacks Tag 01Q3 -/

/-- **Stacks Tag 0B3E with the ampleness of the target module replaced by clause (3) of Stacks Tag
01Q3.** Let `j : X' ⟶ X` be a topological embedding of schemes with `X'` quasi-compact, and let `L`
be an invertible `𝒪_X`-module whose nonvanishing opens `X_s`, for `s` a global section of a
positive tensor power, form a basis for the topology of `X`. Then `j^* L` is ample on `X'`.

Neither `L` ample nor `X` quasi-compact is assumed, and `Stacks.Ample.IsAmple` contains
`CompactSpace`, so this is strictly more general than
`Stacks.SectionExtension.isAmple_pullbackModule`: the three inputs it composes —
`Stacks.AmpleLocallyClosed.isBasisNonvanishing_pullback` (which uses `j` only through inducing),
`Stacks.NonvanishingAffineIntersection.isBasisAffineNonvanishing_of_isBasisNonvanishing` (Stacks
Tag 01PX, unconditional here because Tag 01PV is proved) and
`Stacks.AmpleTheory.isAmple_of_isBasisAffineNonvanishing` — ask for quasi-compactness of the
source alone. Stacks Tag 0H78, the third premise of
`Stacks.AmpleLocallyClosed.isAmple_modulePullback`, is
`Stacks.NonvanishingPullback.sectionPullbackCompatible`. -/
@[ega "II 4.5.2" "partial", ega "II 4.6.13" "special case"]
theorem isAmple_pullbackModule_of_isBasisNonvanishing {X' X : Scheme.{u}} (j : X' ⟶ X)
    (L : X.Modules) [IsInvertibleModule X L] (hemb : Topology.IsEmbedding j)
    (hc : CompactSpace X') (hbasis : Stacks.AmpleTheory.IsBasisNonvanishing X L) :
    IsAmple X' (Stacks.AmpleLocallyClosed.pullbackModule j L) :=
  Stacks.AmpleTheory.isAmple_of_isBasisAffineNonvanishing X' _ hc
    (Stacks.NonvanishingAffineIntersection.isBasisAffineNonvanishing_of_isBasisNonvanishing X' _
      (Stacks.AmpleLocallyClosed.isBasisNonvanishing_pullback j L hemb hbasis
        (Stacks.NonvanishingPullback.sectionPullbackCompatible j L)))

/-- **The local step of Stacks Tag 01VN, with ampleness on the ambient open weakened to clause (3)
of Stacks Tag 01Q3.** Let `i : X ⟶ P` be an immersion, `W` an open of `P` on which the
nonvanishing opens of an invertible `𝒪_P`-module `M` form a basis for the topology, and suppose
`i⁻¹(W)` is quasi-compact. Then a module isomorphic to `i^* M` is ample on `i⁻¹(W)` after
restriction.

This is `Stacks.RelativeVeryAmple.isAmple_restrict_of_immersion` with
`Stacks.RelativeAmpleBasisRoute.isAmple_pullbackModule_of_isBasisNonvanishing` in place of
`Stacks.RelativeVeryAmple.AmplePullbackGap`; the transport onto the restriction of `L` is
unchanged, `Stacks.RelativeVeryAmple.restrictPullbackIso` followed by
`Stacks.RelativeVeryAmple.isAmple_congr`, whose invertibility instance for the *nested* pullback is
supplied by name because instance search does not find it. -/
theorem isAmple_restrict_of_immersion_of_isBasisNonvanishing {X P : Scheme.{u}}
    (i : X ⟶ P) [IsImmersion i] (W : P.Opens) (M : P.Modules) [IsInvertibleModule P M]
    (L : X.Modules) [IsInvertibleModule X L]
    (e : L ≅ (modulePullback i.toLRSHom.toShHom).obj M)
    (hW : Stacks.AmpleTheory.IsBasisNonvanishing W.toScheme
      ((modulePullback W.ι.toLRSHom.toShHom).obj M))
    (hc : CompactSpace (i ⁻¹ᵁ W).toScheme) :
    IsAmple (i ⁻¹ᵁ W).toScheme
      ((modulePullback (i ⁻¹ᵁ W).ι.toLRSHom.toShHom).obj L) := by
  refine (Stacks.RelativeVeryAmple.isAmple_congr _ _
    (hN' := Stacks.InvertiblePullback.isInvertibleModule_pullback (i ∣_ W) _)
    ((modulePullback (i ⁻¹ᵁ W).ι.toLRSHom.toShHom).mapIso e ≪≫
      Stacks.RelativeVeryAmple.restrictPullbackIso i W M)).mpr ?_
  exact isAmple_pullbackModule_of_isBasisNonvanishing (i ∣_ W) _
    (IsPreimmersion.isEmbedding (i ∣_ W)) hc hW

/-! ### The hypothesis of Stacks Tag 01VN, with quasi-compactness of the bundle removed -/

/-- **The hypothesis of Stacks Tag 01VN with relative ampleness of the ambient module weakened to
clause (3) of Stacks Tag 01Q3.** There are a scheme `P` over `S`, an invertible `𝒪_P`-module `M`
whose nonvanishing opens form a basis for the topology of `p⁻¹(V)` for every affine open `V` of
`S`, and an immersion `i : X ⟶ P` over `S` with `L ≅ i^* M`.

`Stacks.RelativeVeryAmple.HasRelativeTwistImmersion` asks instead for
`Stacks.RelativeAmple.IsRelativelyAmple p M`, which contains `QuasiCompact p`; this condition
contains no quasi-compactness at all, and is implied by it
(`hasRelativeBasisImmersion_of_hasRelativeTwistImmersion`). -/
def HasRelativeBasisImmersion {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] : Prop :=
  ∃ (P : Scheme.{u}) (p : P ⟶ S) (M : P.Modules) (hM : IsInvertibleModule P M) (i : X ⟶ P),
    letI : IsInvertibleModule P M := hM
    IsImmersion i ∧ i ≫ p = f ∧
      (∀ V : S.Opens, IsAffineOpen V →
        Stacks.AmpleTheory.IsBasisNonvanishing (p ⁻¹ᵁ V).toScheme
          ((modulePullback (p ⁻¹ᵁ V).ι.toLRSHom.toShHom).obj M)) ∧
      Nonempty (L ≅ (modulePullback i.toLRSHom.toShHom).obj M)

/-- **The twist-immersion hypothesis of Stacks Tag 01VN forces the ambient scheme to be
quasi-compact over the base.** `Stacks.RelativeAmple.IsRelativelyAmple p M` is `QuasiCompact p`
together with the
affine-open clause, so `Stacks.RelativeVeryAmple.HasRelativeTwistImmersion` cannot be instantiated
at an ambient `P` whose structure morphism is not quasi-compact. This is the obstruction described
in the module documentation: `Proj_S(Sym(E)) ⟶ S` is not quasi-compact for a general
quasi-coherent `E`. -/
theorem quasiCompact_of_hasRelativeTwistImmersion {X S : Scheme.{u}} (f : X ⟶ S) (L : X.Modules)
    [IsInvertibleModule X L] (h : Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f L) :
    ∃ (P : Scheme.{u}) (p : P ⟶ S) (i : X ⟶ P), i ≫ p = f ∧ QuasiCompact p := by
  obtain ⟨P, p, M, hM, i, _, hover, hMample, -⟩ := h
  exact ⟨P, p, i, hover, hMample.1⟩

/-- **The weakened hypothesis is implied by the twist-immersion one**, so
`Stacks.RelativeAmpleBasisRoute.isRelativelyAmple_of_hasRelativeBasisImmersion` subsumes
`Stacks.SectionExtension.isRelativelyAmple_of_relativeTwistImmersion`. Relative ampleness of `M`
gives ampleness on each `p⁻¹(V)`, and clause (1) implies clause (3) of Stacks Tag 01Q3
unconditionally, by `Stacks.SectionExtension.isBasisNonvanishing_of_isAmple`. -/
theorem hasRelativeBasisImmersion_of_hasRelativeTwistImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L]
    (h : Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f L) :
    HasRelativeBasisImmersion f L := by
  obtain ⟨P, p, M, hM, i, him, hover, hMample, he⟩ := h
  let _ : IsInvertibleModule P M := hM
  refine ⟨P, p, M, hM, i, him, hover, fun V hV => ?_, he⟩
  exact Stacks.SectionExtension.isBasisNonvanishing_of_isAmple _ _ (hMample.2 V hV)

/-! ### The content of Stacks Tag 01VN -/

/-- **The content of Stacks Tag 01VN, with no premise and with no quasi-compactness asked of the
ambient scheme over the base.** If `f` is quasi-compact and `L` is isomorphic to the pullback along
an immersion over `S` of an invertible module whose nonvanishing opens form a basis for the
topology of the preimage of every affine open of `S`, then `L` is ample relative to `f`.

The proof is `Stacks.RelativeVeryAmple.isRelativelyAmple_of_hasRelativeTwistImmersion`'s: the
preimage `i⁻¹(p⁻¹(V))` is `f⁻¹(V)` by `rfl` once `f` has been replaced by `i ≫ p`, it is
quasi-compact because `f` is and `V` is affine, and everything else is
`Stacks.RelativeAmpleBasisRoute.isAmple_restrict_of_immersion_of_isBasisNonvanishing` at
`W = p⁻¹(V)`. -/
theorem isRelativelyAmple_of_hasRelativeBasisImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : HasRelativeBasisImmersion f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  obtain ⟨P, p, M, hM, i, him, hover, hbasis, ⟨e⟩⟩ := h
  let _ : IsInvertibleModule P M := hM
  let _ : IsImmersion i := him
  subst hover
  refine ⟨hf, fun V hV => ?_⟩
  exact isAmple_restrict_of_immersion_of_isBasisNonvanishing i (p ⁻¹ᵁ V) M L e (hbasis V hV)
    (isCompact_iff_compactSpace.mp (quasiCompact_iff_forall_isAffineOpen.mp hf V hV))

/-- **`Stacks.SectionExtension.isRelativelyAmple_of_relativeTwistImmersion` recovered**, which is
what makes the theorem above a generalisation of the twist-immersion form of Tag 01VN's content
rather than
a variant of it. -/
theorem isRelativelyAmple_of_relativeTwistImmersion {X S : Scheme.{u}} (f : X ⟶ S)
    (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f L) :
    Stacks.RelativeAmple.IsRelativelyAmple f L :=
  isRelativelyAmple_of_hasRelativeBasisImmersion f L hf
    (hasRelativeBasisImmersion_of_hasRelativeTwistImmersion f L h)

/-- **The implication (2) ⟹ (1) of Stacks Tag 01VU on the weakened hypothesis**: if some positive
tensor power of `L` admits an immersion over the base onto a module satisfying clause (3) of Stacks
Tag 01Q3 on every affine preimage, then `L` is ample relative to `f`. This is the theorem above
followed by the relative half of Stacks Tag 01PT,
`Stacks.RelativeVeryAmple.isRelativelyAmple_of_isRelativelyAmple_tensorPowModule`. -/
theorem isRelativelyAmple_of_exists_hasRelativeBasisImmersion_tensorPowModule {X S : Scheme.{u}}
    (f : X ⟶ S) (L : X.Modules) [IsInvertibleModule X L] (hf : QuasiCompact f)
    (h : ∃ d : ℕ, 1 ≤ d ∧ HasRelativeBasisImmersion f (tensorPowModule X L (d : ℤ))) :
    Stacks.RelativeAmple.IsRelativelyAmple f L := by
  obtain ⟨d, hd, hVA⟩ := h
  exact Stacks.RelativeVeryAmple.isRelativelyAmple_of_isRelativelyAmple_tensorPowModule f L d hd
    (isRelativelyAmple_of_hasRelativeBasisImmersion f _ hf hVA)

end Stacks.RelativeAmpleBasisRoute

end

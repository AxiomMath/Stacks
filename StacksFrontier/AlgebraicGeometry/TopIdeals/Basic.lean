module

public import StacksFrontier.AlgebraicGeometry.TopIdeals.Meet
public import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.KilledSupport
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCoherentImage.Basic

/-!
# The top stratum of [Stacks, Tag 01YH]: from one ideal to every ideal

`ConfinedDevissage.property_of_irreducible_support_of_topIdeals` reduces
[Stacks, Tag 01YH] to its hypothesis `htop`: that `P` holds for the direct image of **every**
quasi-coherent sheaf of ideals on an integral closed subscheme whose range is all of `Z₀`. The
source gets `htop` in two steps. [Stacks, Tag 01YE] applied to the module `G` of the tag's
hypothesis (3), together with the length-one condition (3)(c), gives `P` for **one** such direct
image; the last paragraph of the proof then spreads that to every other ideal by intersecting
with it.

**This file is the second step**, and it needs neither [Stacks, Tag 01YE] nor the length
condition. The implementation notes of
`StacksFrontier/AlgebraicGeometry/FullSupport/Residue.lean` call the remaining work there
"sheaf-level plumbing rather than geometry": that is what is discharged here, and the plumbing
turns out to be entirely formal — the second isomorphism theorem of
`./Meet.lean`, plus the fact that a monomorphism cannot enlarge the support.

What is **not** proved here is the one genuinely geometric input the spreading needs, carried as
the hypothesis `hquot`: that the quotient of `𝒪_Z` by a quasi-coherent sheaf of ideals, pushed
forward, is supported strictly inside `Z₀`. On an integral `Z` with generic point `ζ` that holds
exactly for the ideals that are nonzero, since `𝒪_{Z, ζ}` is a field; it is stated as a
hypothesis rather than proved because the only spelling of it available in this repository,
`Stacks.AlgebraicGeometry.Tag01YHFullSupport.supp_eq_univ_of_not_isZero`, is about the support
of the **ideal** and not of the **quotient**, and the passage between them is a stalk
computation for a direct image along a closed immersion that nothing in either tree states in
the direction needed (only `Stacks.AlgebraicGeometry.Tag01YMHigherRank`'s vanishing *off* the
range).

## Main results

* `supp_subset_of_mono`: a monomorphism of modules does not enlarge the support. The repository
  had the epimorphism statement
  (`Stacks.AlgebraicGeometry.IrreducibleDevissage.supp_subset_of_epi`) and not this one.
* `property_pushforward_of_oneIdeal`: **the last paragraph of the proof of
  [Stacks, Tag 01YH]** — `P` on the direct image of one quasi-coherent sheaf of ideals gives
  `P` on the direct image of every other one.
* `property_of_irreducible_support_of_oneIdeal`: the conclusion of [Stacks, Tag 01YH] with
  `htop` replaced by `P` on a **single** ideal direct image, together with `hquot`.

## Implementation notes

`AlgebraicGeometry.Scheme.Modules` is a `def`, so `Mono` and `IsCoherent` in the two spellings
of the category are not interchangeable by instance search; the local
`instance_reducible` attribute and the explicit `preserves_mono_of_preservesLimit` calls below
are the standard workaround, as in
`AlgebraicGeometry.ClosedImmersionCoherentImage`.

The two short exact sequences of the source are not built as `ShortComplex`es twice: the first
is consumed by `ConfinedDevissage.property_sub_of_twoOutOfThree`, which already
packages "`P` on the target and on the cokernel gives `P` on the source", and the second by
`Stacks.AlgebraicGeometry.DevissageBounded.ext_of_twoOutOfThree`, which is the extension clause
of the tag's two-out-of-three hypothesis.

## References

* [Stacks Project, Tag 01YH](https://stacks.math.columbia.edu/tag/01YH)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules

universe u

namespace Stacks.AlgebraicGeometry.Tag01YHTopIdeals

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### A monomorphism does not enlarge the support -/

/-- **A monomorphism of modules does not enlarge the support.** The repository had the
epimorphism statement, `Stacks.AlgebraicGeometry.IrreducibleDevissage.supp_subset_of_epi`, and
not this one; the input it needs is `TopCat.Presheaf.mono_iff_stalk_mono`, together with the
observation that `SheafOfModules.toSheaf` preserves finite limits and hence monomorphisms.

As with the epimorphism statement, `Mono` in the `SheafOfModules` spelling of the category is
not found by instance search from `Mono` in the `X.Modules` spelling, so it is rebuilt by
hand. -/
theorem supp_subset_of_mono {M N : X.Modules} (φ : M ⟶ N) (hφ : Mono φ) :
    SheafOfModules.supp M ⊆ SheafOfModules.supp N := by
  have hm : @Mono (SheafOfModules.{u} X.ringCatSheaf) (inferInstance) M N φ :=
    ⟨fun g h hcomp => hφ.right_cancellation g h hcomp⟩
  have hlim : PreservesFiniteLimits (SheafOfModules.toSheaf X.ringCatSheaf) := inferInstance
  have hms : Mono ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) :=
    CategoryTheory.preserves_mono_of_preservesLimit (SheafOfModules.toSheaf X.ringCatSheaf) φ
  have hst := (TopCat.Presheaf.mono_iff_stalk_mono
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ)).mp hms
  intro x hx
  obtain ⟨a, ha⟩ := hx
  refine ⟨((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
    ((SheafOfModules.toSheaf X.ringCatSheaf).map φ).hom) a, fun hz => ha ?_⟩
  exact ((AddCommGrpCat.mono_iff_injective _).mp (hst x)) (hz.trans (map_zero _).symm)

/-! ### The last paragraph of the proof -/

variable (P : X.Modules → Prop)

/-- **The last paragraph of the proof of [Stacks, Tag 01YH].** Let `i : Z ⟶ X` be a closed
immersion into a locally Noetherian scheme and let `Z₀` be a set containing the support of every
quotient `i_*(𝒪_Z / J)`, strictly, for each quasi-coherent sheaf of ideals `J` of interest —
that is `hquot`. Then `P` on the direct image of **one** quasi-coherent sheaf of ideals gives
`P` on the direct image of **every** one.

The argument is the source's: form the meet `I₀ ⊓ I'` inside `i_* 𝒪_Z`, note that each of
`i_* I₀ / (I₀ ⊓ I')` and `i_* I' / (I₀ ⊓ I')` embeds in the quotient by the *other* ideal
(`Stacks.AlgebraicGeometry.Tag01YHTopIdeals.meetFstCokernelHom` and `meetSndCokernelHom`), hence
is supported strictly inside `Z₀` and has `P` by `hssub`; descend `P` to the meet along the
first sequence and raise it to `i_* I'` along the second.

`hssub` — `P` on every coherent module supported strictly inside `Z₀` — is the first paragraph
of the source's proof, which this repository already has as
`ConfinedDevissage.property_of_supp_ssubset`; it is taken here in its conclusion
form so that no hypothesis of the ambient dévissage leaks into this statement. -/
theorem property_pushforward_of_oneIdeal [IsLocallyNoetherian X]
    {Z₀ : Set X}
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧ (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hssub : ∀ F : X.Modules, F.IsCoherent → SheafOfModules.supp F ⊂ Z₀ → P F)
    {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (I₀ I' : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
    (hI₀ : I₀.toSheafOfModules.IsQuasicoherent)
    (hI' : I'.toSheafOfModules.IsQuasicoherent)
    (hquotI₀ : SheafOfModules.supp
      (cokernel ((Scheme.Modules.pushforward i).map I₀.ι)) ⊂ Z₀)
    (hquotI' : SheafOfModules.supp
      (cokernel ((Scheme.Modules.pushforward i).map I'.ι)) ⊂ Z₀)
    (hPI₀ : P ((Scheme.Modules.pushforward i).obj I₀.toSheafOfModules)) :
    P ((Scheme.Modules.pushforward i).obj I'.toSheafOfModules) := by
  have hpl : PreservesLimitsOfShape WalkingCospan (Scheme.Modules.pushforward i) := inferInstance
  have hmono : ∀ J : (SheafOfModules.unit Z.ringCatSheaf).Submodule,
      Mono ((Scheme.Modules.pushforward i).map J.ι) := fun J =>
    @preserves_mono_of_preservesLimit _ _ _ _ (Scheme.Modules.pushforward i) _ _ J.ι
      hpl.preservesLimit (inferInstanceAs (Mono J.ι))
  have ha := hmono I₀
  have hb := hmono I'
  set a := (Scheme.Modules.pushforward i).map I₀.ι with ha_def
  set b := (Scheme.Modules.pushforward i).map I'.ι with hb_def
  -- Coherence of the four modules that appear.
  have hA : ((Scheme.Modules.pushforward i).obj I₀.toSheafOfModules).IsCoherent :=
    ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit i I₀ hI₀
  have hB : ((Scheme.Modules.pushforward i).obj I'.toSheafOfModules).IsCoherent :=
    ClosedImmersionCoherentImage.isCoherent_pushforward_submodule_unit i I' hI'
  have hD : ((Scheme.Modules.pushforward i).obj
      (SheafOfModules.unit Z.ringCatSheaf)).IsCoherent :=
    ClosedImmersionCoherentImage.isCoherent_pushforward_unit i
  have hCokB : (cokernel b).IsCoherent := IrreducibleDevissage.isCoherent_cokernel' b hB hD
  have hMeet : (meet a b).IsCoherent :=
    have := hA
    have := hCokB
    AlgebraicGeometry.CoherentAbelian.isCoherent_kernel (a ≫ cokernel.π b)
  have hQ₁ : (cokernel (meetFst a b)).IsCoherent :=
    IrreducibleDevissage.isCoherent_cokernel' _ hMeet hA
  have hQ₂ : (cokernel (meetSnd a b)).IsCoherent :=
    IrreducibleDevissage.isCoherent_cokernel' _ hMeet hB
  -- The two quotients are supported strictly inside `Z₀`.
  have hs₁ : SheafOfModules.supp (cokernel (meetFst a b)) ⊂ Z₀ :=
    lt_of_le_of_lt (supp_subset_of_mono (meetFstCokernelHom a b)
      (mono_meetFstCokernelHom a b)) hquotI'
  have hs₂ : SheafOfModules.supp (cokernel (meetSnd a b)) ⊂ Z₀ :=
    lt_of_le_of_lt (supp_subset_of_mono (meetSndCokernelHom a b)
      (mono_meetSndCokernelHom a b)) hquotI₀
  -- Hence both have `P`, and `P` descends to the meet and rises to `i_* I'`.
  have hPmeet : P (meet a b) :=
    ConfinedDevissage.property_sub_of_twoOutOfThree P hexact (meetFst a b) (mono_meetFst a b)
      hMeet hA hQ₁ hPI₀ (hssub _ hQ₁ hs₁)
  exact DevissageBounded.ext_of_twoOutOfThree P hexact
    (ShortComplex.mk (meetSnd a b) (cokernel.π (meetSnd a b)) (cokernel.condition _))
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel (meetSnd a b))
      mono_f := inferInstance
      epi_g := inferInstance }
    hMeet hB hQ₂ hPmeet (hssub _ hQ₂ hs₂)

/-! ### Tag 01YH with `htop` replaced by a single ideal -/

/-- **The conclusion of [Stacks, Tag 01YH] from its own hypotheses, one ideal direct image, and
`hquot`.** Compared with
`ConfinedDevissage.property_of_irreducible_support_of_topIdeals`, the hypothesis
`htop` — `P` on the direct image of *every* quasi-coherent sheaf of ideals from *every* integral
closed subscheme whose range is all of `Z₀` — is weakened to `P` on *one* such direct image, at
the cost of `hquot`.

`hquot` is a statement about supports with no `P` in it, and it is the only thing between this
and `htop`; `hone` is what [Stacks, Tag 01YE] together with the length-one condition (3)(c) of
the tag is for. The quantification over `Z` is kept, because the dévissage meets an arbitrary
integral closed subscheme with range `Z₀` and this repository does not transport a quasi-coherent
ideal along the isomorphism identifying two such. -/
theorem property_of_irreducible_support_of_oneIdeal [IsNoetherian X]
    (hsplit : DevissageNoetherian.HasSupportSplitting X)
    (hirr : ConfinedDevissage.HasIrreducibleDevissageIn X)
    {Z₀ : Set X}
    (hexact : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent →
      ((P S.X₁ ∧ P S.X₂ → P S.X₃) ∧ (P S.X₁ ∧ P S.X₃ → P S.X₂) ∧
        (P S.X₂ ∧ P S.X₃ → P S.X₁)))
    (hproper : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z], Set.range i.base ⊂ Z₀ →
      ∀ (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule)
        [I.toSheafOfModules.IsQuasicoherent],
        P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules))
    (hquot : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z], Set.range i.base = Z₀ →
      ∀ (J : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
        J.toSheafOfModules.IsQuasicoherent →
        SheafOfModules.supp (cokernel ((Scheme.Modules.pushforward i).map J.ι)) ⊂ Z₀)
    (hone : ∀ (Z : Scheme.{u}) (i : Z ⟶ X) [IsClosedImmersion i]
      [IsIntegral Z], Set.range i.base = Z₀ →
      ∃ (I₀ : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
        I₀.toSheafOfModules.IsQuasicoherent ∧
        P ((Scheme.Modules.pushforward i).obj I₀.toSheafOfModules))
    (G : X.Modules) (hG : G.IsCoherent) (hPG : P G) :
    ∀ F : X.Modules, F.IsCoherent → SheafOfModules.supp F ⊆ Z₀ → P F := by
  refine ConfinedDevissage.property_of_irreducible_support_of_topIdeals P hsplit hirr hexact hproper
    (fun Z i _ _ hrange I hI => ?_) G hG hPG
  obtain ⟨I₀, hI₀, hPI₀⟩ := hone Z i hrange
  exact property_pushforward_of_oneIdeal P hexact
    (ConfinedDevissage.property_of_supp_ssubset P hsplit hirr
      (DevissageBounded.property_terminal_of_twoOutOfThree P hexact G hG hPG)
      (DevissageBounded.ext_of_twoOutOfThree P hexact) hproper)
    i I₀ I hI₀ hI (hquot Z i hrange I₀ hI₀) (hquot Z i hrange I hI) hPI₀

end Stacks.AlgebraicGeometry.Tag01YHTopIdeals

end

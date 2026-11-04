module

public import StacksFrontier.AlgebraicGeometry.PartTwo.Basic
public import StacksFrontier.AlgebraicGeometry.DiagonalHy.Basic
public import StacksFrontier.AlgebraicGeometry.DiagonalCotangentTransport.Basic
public import StacksFrontier.AlgebraicGeometry.LeibnizDerivation.Affine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# [Stacks, Tag 08S2]: the relative differentials are the conormal sheaf of the diagonal

For a morphism of schemes `f : X ⟶ S`, the sheaf of relative differentials `Ω_{X/S}` is
canonically isomorphic to the conormal sheaf of the diagonal `Δ : X ⟶ X ×_S X`, and the
isomorphism sends `d b` to the conormal class of `p₂^♯ b - p₁^♯ b`. Both assertions were already
written in `StacksDraft.AlgebraicGeometry.F3.LeibnizDerivation.Affine`, each carrying the single
hypothesis `IsIso (Stacks.LeibnizDerivation.toConormal f)`, which is why no tag was attached
there. **This file discharges that hypothesis**, and both clauses of
[Stacks, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2) are restated here with no
hypothesis at all: `f` is an arbitrary morphism of schemes, and nothing is affine, separated,
Noetherian or quasi-compact.

## Route

`Stacks.LeibnizDerivation.isIso_toConormal_of_forall_isIso_kaehlerToConormal` reduces the
hypothesis to `IsIso (Stacks.LeibnizDerivation.kaehlerToConormal f V U hUV)` for an affine open
`U` of `X` lying inside the preimage of an affine open `V` of `S`. Writing `A = Γ(X, U)`,
`R = Γ(S, V)`, `B = Γ(X ×_S X, ambientChart f U)` and `I = RingHom.ker (diagAppLE f U)` — the
ideal of the diagonal in the ambient chart — the two halves that had been built separately are
*two bijections onto the same `I ⧸ I²`*:

* the **sheaf side**, `exists_conormalComparison`: the sections over the ambient chart of the
  direct image along the diagonal of the conormal sheaf are `I ⧸ I²`, and the conormal class
  `Stacks.LeibnizDerivation.cls f U b` goes to the class of `p₂^♯ b - p₁^♯ b`. The bijection is
  `Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent` at the diagonal, with the
  presentation data of `Stacks.DiagonalPresentation.exists_diagonalPresentation_ker`; the formula
  is `Stacks.Tag01R3PartTwo.conormalAffineSectionsIsoCotangent_toCotangent`, the part (2)
  generator formula of [Stacks, Tag 01R3] at an arbitrary immersion, whose naming hypothesis at
  the diagonal is `Stacks.Tag08S2DiagonalHy.appLE_coborderRange_delta` together with
  `Stacks.LeibnizDerivation.ι_deltaIdealSection`;
* the **ring side**, `exists_kaehlerComparison`: `Ω[A⁄R]` is `I ⧸ I²`, carrying `d b` to the
  class of the *same* ring element. This is
  `Stacks.DiagonalCotangentTransport.cotangentEquiv` across
  `Stacks.DiagonalChart.tensorIsoChart`.

What makes the two comparable is **one scalar action**: both are semilinear for
`a ↦ p₁^♯ a`. On the sheaf side that is `pushSection_smul`; on the ring side it is
`KaehlerDifferential`'s own scalar tower through `A ⊗[R] A` together with
`Stacks.DiagonalChart.includeLeft_tensorIsoChart`. The universal differentials span `Ω[A⁄R]`
over `A`, so `bijective_of_spanning` concludes that the two agree everywhere, and
`kaehlerToConormal` inherits bijectivity.

## The module-structure step, and why no module structure has to be bridged

The step the earlier files record as owed is that
`conormalAffineSectionsIsoCotangent` is `B`-linear while `kaehlerToConormal` lives in
`ModuleCat A`. It is taken in `pushSection_smul`, and the shape that makes it cheap is worth
recording: **`bijective_of_spanning` takes the scalar action as an arbitrary function
`sc : A → N → N`**, so no `A`-module structure on `I ⧸ I²` is needed and the `B`-structure and
the `A ⊗[R] A`-structure never have to be identified — only *one* action for which both sides
are semilinear. The action is `p₁^♯`, and the diagonal's comorphism retracts it
(`Stacks.DiagonalChart.fst_appLE_comp_diagAppLE`), which is the whole content of
`Stacks.LeibnizDerivation.surjective_diagRes_appTop` that is actually used.

## How the `whnf` timeout was beaten without a compiler option

`StacksFrontier.AlgebraicGeometry.DiagonalHy.Basic` records that the assembly is a single
`refine` whose *proof* goes through while its *statement* times out at `whnf` on the default
budget, because substituting `i := pullback.diagonal f` and
`V := Stacks.LeibnizDerivation.ambientChart f U` into the part (2) formula drives `whnf`
through `CategoryTheory.Limits.getLimitCone`. Two devices avoid it, and together they cost
nothing:

* **the comparison enters as an opaque local constant.** `exists_conormalComparison` and
  `exists_kaehlerComparison` are *existential*, so their consumers `obtain` a local `Ψ` and `g`
  whose bodies Lean never unfolds. No statement in the assembly mentions
  `conormalAffineSectionsIsoCotangent` or `cotangentEquiv`;
* **every statement that does mention the diagonal is kept small by reducible abbreviations with
  declared types** (`srcSection`, `pushSection`, `psmul`, `projOne`, `projTwo`), and every
  substitution of the diagonal happens inside an *application*, where the expected type guides
  unification instead of reduction.

A third device is needed for a different reason: `Stacks.LeibnizDerivation.toXRing` and `psmul`
exist because a scalar action written at the `Γ(Y, V)` spelling fails to synthesize `HSMul` at
all, and `rw` across that gap reports "did not find an occurrence" on a pattern that is present.
Every `•` below is therefore produced by a `map_smul`.

Relatedly, `le_rfl` is not safely usable for
`chart f U ≤ Δ.coborderRange.ι ⁻¹ᵁ ambientChart f U` even though the two opens are `rfl`-equal;
`Stacks.LeibnizDerivation.coborderRange_ι_preimage_ambientChart _ _ |>.ge` is the proof to pass.

## Main results

* `Stacks.Tag08S2Assembly.bijective_of_spanning`: the comparison principle — a map out of the
  Kähler differentials is bijective once it becomes a known bijection after an additive
  comparison semilinear for one abstract scalar action.
* `Stacks.Tag08S2Assembly.pushSection_smul`: the module-structure step, at an arbitrary
  morphism of schemes.
* `Stacks.Tag08S2Assembly.exists_conormalComparison` and
  `Stacks.Tag08S2Assembly.exists_kaehlerComparison`: the two halves, each with its generator
  formula and its semilinearity.
* `Stacks.Tag08S2Assembly.isIso_kaehlerToConormal`: **the affine comparison map of
  [Stacks, Tag 08S2] is invertible** — the single statement
  `StacksDraft.AlgebraicGeometry.F3.LeibnizDerivation.Affine` records as separating it from the
  full statement.
* `Stacks.Tag08S2Assembly.isIso_toConormal`: hence `Ω_{X/S} ⟶ C_Δ` is an isomorphism.
* `Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal` and
  `Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal_apply`: **the two clauses of
  [Stacks, Tag 08S2]**, unconditionally.

## Vocabulary

The notions of the tagged statements are realized as follows: the module of relative
differentials of Tag 01US is `AlgebraicGeometry.Scheme.Hom.relativeDifferentials` and its
universal derivation is `AlgebraicGeometry.Scheme.Hom.universalRelativeDerivation`; the conormal
sheaf of Tag 01R2 is `Stacks.Conormal.conormalSheaf` and the quotient map of Tag 01R3 is
`Stacks.Conormal.conormalQuotientMap`
(`StacksDraft.AlgebraicGeometry.F3.Conormal.IdealSheafComparison`); the ideal sheaf of Tag 01C2
is `Stacks.ClosedImmersion.idealSheaf`.

Both labels of [Stacks, Tag 08S2] are attached here, each on the one declaration stating it:
the bare label on the comparison isomorphism and `"canonical quotient formula"` on the formula
for its hom. Neither carries a hypothesis the tag lacks.

## Two notes elsewhere that are false

* `StacksFrontier.AlgebraicGeometry.Locality.Sections`, "What is not done", withholds the
  part (2) tags on the ground that "nothing says two factorizations give the same answer". That
  is false: `Stacks.Conormal.OpenFactorizations.generator_eq_of_two_factorizations`
  (`ConormalOpenFactorizations/Compatibility.lean:226`) says exactly that for an arbitrary
  ambient section.
* the note in `StacksDraft.AlgebraicGeometry.F3.DiagonalQuotientPresentation.Basic` that no
  transport of `Ideal.Cotangent` along a ring isomorphism exists at this pin is false — but it
  is **already corrected in the tree**: that file's "What is not done" now records the
  refutation itself and names `Ideal.mapCotangent`.

## Universe situation

A single universe `u`, as in the tagged statements.

## References

* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 01R3](https://stacks.math.columbia.edu/tag/01R3)
* [Stacks Project, Tag 01UT](https://stacks.math.columbia.edu/tag/01UT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction TensorProduct

universe u

namespace Stacks.Tag08S2Assembly

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : X.Opens)

/-! ### The two projections' comorphisms on the ambient chart -/

/-- `p₁^♯ b` as a section of the ambient chart. -/
noncomputable abbrev projOne (b : Γ(X, U)) :
    Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U) :=
  ((pullback.fst f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
    (Stacks.LeibnizDerivation.ambientChart_le_fst_preimage f U)).hom b

/-- `p₂^♯ b` as a section of the ambient chart. -/
noncomputable abbrev projTwo (b : Γ(X, U)) :
    Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U) :=
  ((pullback.snd f f).appLE U (Stacks.LeibnizDerivation.ambientChart f U)
    (Stacks.LeibnizDerivation.ambientChart_le_snd_preimage f U)).hom b

/-- The comorphism of the diagonal retracts the first projection's. -/
theorem diagAppLE_projOne (b : Γ(X, U)) :
    ((Stacks.DiagonalChart.diagAppLE f U).hom) (projOne f U b) = b :=
  congr($(Stacks.DiagonalChart.fst_appLE_comp_diagAppLE f U) b)

/-- The comorphism of the diagonal retracts the second projection's. -/
theorem diagAppLE_projTwo (b : Γ(X, U)) :
    ((Stacks.DiagonalChart.diagAppLE f U).hom) (projTwo f U b) = b :=
  congr($(Stacks.DiagonalChart.snd_appLE_comp_diagAppLE f U) b)

/-! ### Transports along an equality of opens -/

section Transport

/-- A restriction map of the structure sheaf along a hom from an open to itself is the
identity. -/
theorem presheaf_map_self {Y : Scheme.{u}} {a : Y.Opens} (g : a ⟶ a) (t : Γ(Y, a)) :
    (Y.presheaf.map g.op).hom t = t := by
  rw [Subsingleton.elim g (𝟙 a)]
  simp

/-- **A restriction map of a sheaf of modules along an equality of opens is bijective**, its
inverse being the restriction map along the reversed equality. -/
theorem bijective_map_eqToHom {Y : Scheme.{u}} (M : Y.Modules) {a b : Y.Opens} (h : a = b) :
    Function.Bijective (fun z : M.val.obj (.op b) => ((M.val.map (eqToHom h).op).hom z)) := by
  have key : ∀ {a b : Y.Opens} (h : a = b) (z : M.val.obj (.op b)),
      ((M.val.map (eqToHom h.symm).op).hom ((M.val.map (eqToHom h).op).hom z)) = z := fun h z =>
    (Stacks.Tag08S2Locality.map_map M (eqToHom h.symm) (eqToHom h) z).trans
      (Stacks.Tag08S2Locality.map_self M _ z)
  exact Function.bijective_iff_has_inverse.2
    ⟨fun w => ((M.val.map (eqToHom h.symm).op).hom w), key h, key h.symm⟩

/-- **Transporting the sections of the preimage open back along the equality undoes the
`appLE`.** For `i ⁻¹ᵁ V = W`, the comorphism of `i` on `V` followed by restriction to `W`, read
back at `i ⁻¹ᵁ V`, is the comorphism itself. -/
theorem map_appLE_eq_app {Z Y : Scheme.{u}} (i : Z ⟶ Y) (V : Y.Opens) {W : Z.Opens}
    (hW : i ⁻¹ᵁ V = W) (c : Γ(Y, V)) :
    (Z.presheaf.map (eqToHom hW).op).hom ((i.appLE V W hW.ge).hom c) =
      (i.app V).hom c := by
  subst hW
  rw [Scheme.Hom.appLE_eq_app]
  exact presheaf_map_self _ _

end Transport

/-! ### Sections over an open equal to a preimage, read as sections of a direct image

This is where the module-structure step of [Stacks, Tag 08S2] is taken, and it is taken
generically. Three spellings of one type are in play and instance search crosses none of them
(see the "Transparency gotchas" of `StacksDraft.AlgebraicGeometry.F3.LeibnizDerivation.Basic`):
the sections over `W`, the sections over `i ⁻¹ᵁ V` for `i ⁻¹ᵁ V = W`, and the sections over `V`
of the direct image. So each is given a *declared* type by a reducible abbreviation, and every
`•` below is produced by a `map_smul`, never written by hand. -/

section PushSection

variable {Z Y : Scheme.{u}} (i : Z ⟶ Y) (M : SheafOfModules.{u} Z.ringCatSheaf) (V : Y.Opens)
  {W : Z.Opens} (hW : i ⁻¹ᵁ V = W)

/-- A section over `W` transported to `i ⁻¹ᵁ V`, declared at the source's spelling. -/
noncomputable abbrev srcSection (z : M.val.obj (.op W)) : M.val.obj (.op (i ⁻¹ᵁ V)) :=
  ((M.val.map (eqToHom hW).op).hom z)

/-- **A scalar acting on a section of a presheaf of modules, written at the one spelling
instance search can see.** `M.obj O` is declared as a `ModuleCat (R.obj O)`, so a `•` written
here resolves by unification against `R.obj O` and nothing has to be unfolded; written at any
of the four equivalent spellings of the ring of sections of a scheme it does not resolve at all
(`StacksDraft.AlgebraicGeometry.F3.LeibnizDerivation.Basic`, "Transparency gotchas"). Every
scalar action below goes through this abbreviation. -/
noncomputable abbrev psmul {C : Type*} [Category C] {R : Cᵒᵖ ⥤ RingCat.{u}}
    (M : PresheafOfModules.{u} R) {O : Cᵒᵖ} (r : R.obj O) (z : M.obj O) : M.obj O := r • z

/-- The same transport, declared at the direct image's spelling — the source of
`Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent`. -/
noncomputable abbrev pushSection (z : M.val.obj (.op W)) :
    ((modulePushforward i.toLRSHom.toShHom).obj M).val.obj (.op V) :=
  ((M.val.map (eqToHom hW).op).hom z)

/-- `pushSection` is bijective, being a restriction map along an equality of opens. -/
theorem bijective_pushSection : Function.Bijective (pushSection i M V hW) :=
  bijective_map_eqToHom M hW

/-- **A map out of the sections of a direct image is semilinear for the transport.** For
`c : Γ(Y, V)`, the action of `c` on the sections over `V` of the direct image is the action of
its restriction `i.appLE V W` on the sections over `W`. Both `•`s come from a `map_smul` and
`map_appLE_eq_app` identifies the two scalars. -/
theorem pushSection_smul {N : ModuleCat.{u} ↑(Stacks.LeibnizDerivation.xRing V)}
    (φ : ((modulePushforward i.toLRSHom.toShHom).obj M).val.obj (.op V) ⟶ N)
    (c : Γ(Y, V)) (z : M.val.obj (.op W)) :
    φ.hom (pushSection i M V hW
        (psmul M.val (Stacks.LeibnizDerivation.toXRing ((i.appLE V W hW.ge).hom c)) z)) =
      Stacks.LeibnizDerivation.toXRing c • φ.hom (pushSection i M V hW z) := by
  refine Eq.trans ?_ (map_smul φ.hom (Stacks.LeibnizDerivation.toXRing c)
    (pushSection i M V hW z))
  refine congrArg (fun t => φ.hom t) ?_
  refine Eq.trans (PresheafOfModules.map_smul _ _
    (Stacks.LeibnizDerivation.toXRing ((i.appLE V W hW.ge).hom c)) z) ?_
  exact congrArg (fun r => psmul M.val r (srcSection i M V hW z))
    (map_appLE_eq_app i V hW c)

end PushSection

/-! ### The conormal class, read at the ambient chart -/

/-- **The conormal class of `p₂^♯ b - p₁^♯ b` over `U`, transported to the preimage of the
ambient chart, is the quotient generator the part (2) formula of [Stacks, Tag 01R3] computes.**
Both sides restrict one and the same quotient value along a hom of opens from
`Δ ⁻¹ᵁ ambientChart f U` to `Δ.liftCoborder ⁻¹ᵁ chart f U`, and homs in a poset category agree.
The chart is `Δ.coborderRange.ι ⁻¹ᵁ ambientChart f U` by `rfl`
(`Stacks.LeibnizDerivation.coborderRange_ι_preimage_ambientChart`), so no transport of the inner
open is needed. -/
theorem srcSection_cls (b : Γ(X, U)) :
    srcSection (pullback.diagonal f) (Stacks.Conormal.conormalSheaf (pullback.diagonal f))
        (Stacks.LeibnizDerivation.ambientChart f U)
        (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U)
        (Stacks.LeibnizDerivation.cls f U b) =
      ((Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val.map
          (eqToHom (Stacks.Tag01R3PartTwo.preimage_eq_liftCoborder_preimage
            (pullback.diagonal f) (Stacks.LeibnizDerivation.ambientChart f U))).op).hom
        (Stacks.LeibnizDerivation.quotientApp f
          ((pullback.diagonal f).coborderRange.ι ⁻¹ᵁ
            Stacks.LeibnizDerivation.ambientChart f U)
          (Stacks.LeibnizDerivation.deltaIdealSection f U b)) := by
  refine Eq.trans (Stacks.Tag08S2Locality.map_map _
    (eqToHom (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U))
    (homOfLE (Stacks.LeibnizDerivation.le_chart_preimage f U)) _) ?_
  exact PresheafOfModules.congr_map_apply
    (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val
    (congrArg Quiver.Hom.op (Subsingleton.elim _ _)) _

/-- **The sheaf side of [Stacks, Tag 08S2], as a bijection with its generator formula.** For an
affine open `U` of `X` lying over an affine open `V` of `S`, the sections over the ambient chart
of the direct image along the diagonal of the conormal sheaf are bijectively `I ⧸ I²` for `I`
the ideal of the diagonal in the chart, and the bijection carries the conormal class of a
section `b` to the class of the ring element `p₂^♯ b - p₁^♯ b`.

The bijection is
`Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent` at the diagonal, which the
presentation data of `Stacks.DiagonalPresentation.exists_diagonalPresentation_ker` makes
available, and the formula is
`Stacks.Tag01R3PartTwo.conormalAffineSectionsIsoCotangent_toCotangent` — the part (2) generator
formula of [Stacks, Tag 01R3] at an arbitrary immersion — with its naming hypothesis supplied by
`appLE_delta_eq_deltaAt` and `Stacks.LeibnizDerivation.ι_deltaIdealSection`.

It is stated as an existential so that the comparison enters the assembly below as an opaque
local constant: the five-fold composite it unfolds to is what makes `whnf` on a statement
mentioning it explicitly run through `CategoryTheory.Limits.getLimitCone`. -/
theorem exists_conormalComparison {V : S.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    ∃ Ψ : ((modulePushforward (pullback.diagonal f).toLRSHom.toShHom).obj
          (Stacks.Conormal.conormalSheaf (pullback.diagonal f))).val.obj
          (.op (Stacks.LeibnizDerivation.ambientChart f U)) ⟶
        ModuleCat.of Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U)
          (RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom).Cotangent,
      Function.Bijective Ψ.hom ∧
        ∀ b : Γ(X, U),
          Ψ.hom (pushSection (pullback.diagonal f)
              (Stacks.Conormal.conormalSheaf (pullback.diagonal f))
              (Stacks.LeibnizDerivation.ambientChart f U)
              (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U)
              (Stacks.LeibnizDerivation.cls f U b)) =
            (RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom).toCotangent
              ⟨projTwo f U b - projOne f U b,
                Stacks.Tag08S2DiagonalHy.delta_mem_ker_diagAppLE f U b⟩ := by
  obtain ⟨e, he⟩ := Stacks.DiagonalPresentation.exists_diagonalPresentation_ker f U hV hU hUV
  refine ⟨(Stacks.Conormal.CotangentAppIso.conormalAffineSectionsIsoCotangent
      (pullback.diagonal f) (Stacks.LeibnizDerivation.ambientChart f U)
      (Stacks.LeibnizDerivation.isAffineOpen_ambientChart f U hV hU hUV) _ e he).hom,
    ConcreteCategory.bijective_of_isIso _, fun b => ?_⟩
  refine Eq.trans ?_ (Stacks.Tag01R3PartTwo.conormalAffineSectionsIsoCotangent_toCotangent
    (pullback.diagonal f) (Stacks.LeibnizDerivation.ambientChart f U)
    (Stacks.LeibnizDerivation.isAffineOpen_ambientChart f U hV hU hUV) _ e he
    ⟨projTwo f U b - projOne f U b, Stacks.Tag08S2DiagonalHy.delta_mem_ker_diagAppLE f U b⟩
    (Stacks.LeibnizDerivation.deltaIdealSection f U b)
    ((Stacks.Tag08S2DiagonalHy.appLE_coborderRange_delta f U b).trans
      (Stacks.LeibnizDerivation.ι_deltaIdealSection f U b).symm))
  exact congrArg _ (srcSection_cls f U b)

/-! ### The ring side: the chart's `I ⧸ I²` is `Ω[Γ(X, U)⁄Γ(S, V)]`, semilinearly -/

/-- **`Stacks.DiagonalCotangentTransport.cotangentEquiv` is semilinear over the algebra map.**
It is linear over the source ring by construction, and the target's action by that ring is the
action of its image, which is `IsScalarTower.algebraMap_smul`. -/
theorem cotangentEquiv_smul {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (hbij : Function.Bijective (algebraMap A B)) (J : Ideal A) (I : Ideal B)
    (hJI : Ideal.comap (algebraMap A B) I = J) (h : J ≤ Ideal.comap (algebraMap A B) I)
    (t : A) (ω : J.Cotangent) :
    Stacks.DiagonalCotangentTransport.cotangentEquiv hbij J I hJI h (t • ω) =
      (algebraMap A B t) •
        Stacks.DiagonalCotangentTransport.cotangentEquiv hbij J I hJI h ω := by
  rw [map_smul]
  exact (IsScalarTower.algebraMap_smul B t _).symm

/-- **The ring side of [Stacks, Tag 08S2], as a bijection with its generator formula and its
semilinearity.** The conormal module of the ideal of the diagonal in the ambient chart is
`Ω[Γ(X, U)⁄Γ(S, V)]`; the identification carries `d b` to the class of `p₂^♯ b - p₁^♯ b`, and it
carries the action of `a : Γ(X, U)` to the action of `p₁^♯ a`.

This is `Stacks.DiagonalCotangentTransport.exists_addEquiv_kaehlerCotangentChart` with the
semilinearity retained: that statement discards it, phrasing the identification additively,
whereas the assembly needs exactly one scalar action for which both sides of the comparison are
semilinear. The action of `a` on `Ω[A⁄R]` is the action of `a ⊗ 1` by
`KaehlerDifferential`'s own scalar tower, `tensorIsoChart` carries `a ⊗ 1` to `p₁^♯ a`
(`Stacks.DiagonalChart.includeLeft_tensorIsoChart`), and `cotangentEquiv_smul` moves the scalar
across. -/
@[sga "6 VIII 2.2", sga "7 VI 5.5" "(V), special case"]
theorem exists_kaehlerComparison {V : S.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) [Algebra Γ(S, V) Γ(X, U)]
    (halg : CommRingCat.ofHom (algebraMap Γ(S, V) Γ(X, U)) = f.appLE V U hUV) :
    ∃ g : Ω[Γ(X, U)⁄Γ(S, V)] →+
        (RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom).Cotangent,
      Function.Bijective g ∧
        (∀ (a : Γ(X, U)) (ω : Ω[Γ(X, U)⁄Γ(S, V)]), g (a • ω) = projOne f U a • g ω) ∧
          ∀ b : Γ(X, U), g (KaehlerDifferential.D Γ(S, V) Γ(X, U) b) =
            (RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom).toCotangent
              ⟨projTwo f U b - projOne f U b,
                Stacks.Tag08S2DiagonalHy.delta_mem_ker_diagAppLE f U b⟩ := by
  let _inst : Algebra ((Γ(X, U) : Type u) ⊗[Γ(S, V)] Γ(X, U))
      Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U) :=
    RingHom.toAlgebra (Stacks.DiagonalChart.tensorIsoChart f V U hUV halg hV hU).hom.hom
  have hbij : Function.Bijective
      (algebraMap ((Γ(X, U) : Type u) ⊗[Γ(S, V)] Γ(X, U))
        Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U)) :=
    ConcreteCategory.bijective_of_isIso
      (Stacks.DiagonalChart.tensorIsoChart f V U hUV halg hV hU).hom
  have hJI : Ideal.comap
        (algebraMap ((Γ(X, U) : Type u) ⊗[Γ(S, V)] Γ(X, U))
          Γ(Limits.pullback f f, Stacks.LeibnizDerivation.ambientChart f U))
        (RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom) =
      KaehlerDifferential.ideal Γ(S, V) Γ(X, U) :=
    (Stacks.DiagonalChart.kaehlerIdeal_eq_comap_ker_diagAppLE f V U hUV halg hV hU).symm
  let e := Stacks.DiagonalCotangentTransport.cotangentEquiv hbij
    (KaehlerDifferential.ideal Γ(S, V) Γ(X, U))
    (RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom) hJI hJI.ge
  refine ⟨e.toLinearMap.toAddMonoidHom, e.bijective, ?_, ?_⟩
  · intro a ω
    refine Eq.trans (congrArg e
      (IsScalarTower.algebraMap_smul ((Γ(X, U) : Type u) ⊗[Γ(S, V)] Γ(X, U)) a ω).symm) ?_
    refine Eq.trans (cotangentEquiv_smul hbij _ _ hJI hJI.ge
      (algebraMap Γ(X, U) ((Γ(X, U) : Type u) ⊗[Γ(S, V)] Γ(X, U)) a) ω) ?_
    exact congrArg (fun r => r • e ω)
      (congr($(Stacks.DiagonalChart.includeLeft_tensorIsoChart f V U hUV halg hV hU) a))
  · intro b
    refine Eq.trans (congrArg e
      (Stacks.DiagonalConormal.toCotangent_one_tmul_sub_tmul_one Γ(S, V) Γ(X, U) b).symm) ?_
    refine Eq.trans (Stacks.DiagonalCotangentTransport.cotangentEquiv_toCotangent hbij _ _
      hJI hJI.ge ((1 : Γ(X, U)) ⊗ₜ[Γ(S, V)] b - b ⊗ₜ[Γ(S, V)] (1 : Γ(X, U)))
      (Stacks.DiagonalConormal.one_tmul_sub_tmul_one_mem_ker Γ(S, V) Γ(X, U) b) ?_) ?_
    · exact (Stacks.DiagonalChart.tensorIsoChart_one_tmul_sub_tmul_one f V U hUV halg hV hU b).symm
        ▸ Stacks.Tag08S2DiagonalHy.delta_mem_ker_diagAppLE f U b
    · exact congrArg (RingHom.ker (Stacks.DiagonalChart.diagAppLE f U).hom).toCotangent
        (Subtype.ext
          (Stacks.DiagonalChart.tensorIsoChart_one_tmul_sub_tmul_one f V U hUV halg hV hU b))

/-! ### The spanning argument -/

section Spanning

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {N : Type u} [AddCommGroup N]

/-- **A map out of the Kähler differentials is bijective as soon as it becomes a known
bijection after an injective additive comparison.** Both `β ∘ k` and `g` are additive and
`A`-semilinear over one and the same abstract scalar action `sc` on `N`, and they agree on the
universal differentials; those span `Ω[A⁄R]` over `A`, so the two maps agree everywhere, and
`k` inherits bijectivity from `g` through `β`.

The scalar action `sc` is an arbitrary function: no module structure on `N` over `A` is needed,
only that *one* action makes both comparisons semilinear. That is what lets the two sides of
[Stacks, Tag 08S2] — one a sheaf-theoretic identification linear over the sections of the
ambient chart, the other a ring-theoretic one linear over the tensor square — be compared
without bridging the two module structures. -/
theorem bijective_of_spanning {M : ModuleCat.{u} A} (k : Ω[A⁄R] →ₗ[A] M) (β : M → N)
    (g : Ω[A⁄R] →+ N)
    (sc : A → N → N) (hβ0 : β 0 = 0) (hβadd : ∀ x y : M, β (x + y) = β x + β y)
    (hβ : Function.Bijective β) (hg : Function.Bijective g)
    (hβs : ∀ (a : A) (z : M), β (a • z) = sc a (β z))
    (hgs : ∀ (a : A) (ω : Ω[A⁄R]), g (a • ω) = sc a (g ω))
    (hgen : ∀ b : A, β (k (KaehlerDifferential.D R A b)) = g (KaehlerDifferential.D R A b)) :
    Function.Bijective k := by
  have key : ∀ ω : Ω[A⁄R], β (k ω) = g ω := by
    intro ω
    have hmem : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D R A)) := by
      rw [KaehlerDifferential.span_range_derivation]; trivial
    induction hmem using Submodule.span_induction with
    | mem x hx => obtain ⟨b, rfl⟩ := hx; exact hgen b
    | zero => rw [map_zero, hβ0, map_zero]
    | add x y _ _ hx hy => rw [map_add, hβadd, map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hβs, hx, hgs]
  refine ⟨fun x y hxy => hg.1 ?_, fun m => ?_⟩
  · exact (key x).symm.trans (by rw [hxy]; exact key y)
  · obtain ⟨ω, hω⟩ := hg.2 (β m)
    exact ⟨ω, hβ.1 ((key ω).trans hω)⟩

end Spanning

/-! ### The affine comparison of [Stacks, Tag 08S2] is an isomorphism -/

/-- **The affine comparison map of [Stacks, Tag 08S2] is invertible**, for an affine open `U` of
`X` lying inside the preimage of an affine open `V` of `S`. This is the single statement that
`StacksDraft.AlgebraicGeometry.F3.LeibnizDerivation.Affine` records as separating it from the
full statement of the tag.

`exists_conormalComparison` and `exists_kaehlerComparison` identify the conormal sections over
`U` and the Kähler differentials with one and the same `I ⧸ I²` — the conormal module of the
ideal of the diagonal in the ambient chart — carrying `cls f U b` and `d b` to the class of the
*same* ring element `p₂^♯ b - p₁^♯ b`. Both identifications are semilinear for the action of
`p₁^♯ a`, so `bijective_of_spanning` concludes. -/
@[ega "IV 17.13.5" "special case", sga "6 VIII 2.2", sga "7 VI 5.5" "(V), special case"]
theorem isIso_kaehlerToConormal {V : S.Opens} (hV : IsAffineOpen V) (hU : IsAffineOpen U)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    IsIso (Stacks.LeibnizDerivation.kaehlerToConormal f V U hUV) := by
  let _inst : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  obtain ⟨Ψ, hΨbij, hΨgen⟩ := exists_conormalComparison f U hV hU hUV
  obtain ⟨g, hgbij, hgs, hggen⟩ := exists_kaehlerComparison f U hV hU hUV rfl
  refine (ConcreteCategory.isIso_iff_bijective
    (Stacks.LeibnizDerivation.kaehlerToConormal f V U hUV)).2 ?_
  refine bijective_of_spanning (Stacks.LeibnizDerivation.kaehlerToConormal f V U hUV).hom
    (fun z => Ψ.hom (pushSection (pullback.diagonal f)
      (Stacks.Conormal.conormalSheaf (pullback.diagonal f))
      (Stacks.LeibnizDerivation.ambientChart f U)
      (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U) z))
    g (fun a w => projOne f U a • w) ?_ (fun x y => ?_)
    (hΨbij.comp (bijective_map_eqToHom (Stacks.Conormal.conormalSheaf (pullback.diagonal f))
      (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U)))
    hgbij (fun a z => ?_) hgs (fun b => ?_)
  · exact (congrArg Ψ.hom (map_zero _)).trans (map_zero _)
  · exact (congrArg Ψ.hom (map_add _ _ _)).trans (map_add _ _ _)
  · refine Eq.trans ?_ (pushSection_smul (pullback.diagonal f)
      (Stacks.Conormal.conormalSheaf (pullback.diagonal f))
      (Stacks.LeibnizDerivation.ambientChart f U)
      (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U) Ψ (projOne f U a) z)
    exact congrArg (fun r => Ψ.hom (pushSection (pullback.diagonal f)
        (Stacks.Conormal.conormalSheaf (pullback.diagonal f))
        (Stacks.LeibnizDerivation.ambientChart f U)
        (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U)
        (psmul (Stacks.Conormal.conormalSheaf (pullback.diagonal f)).val
          (Stacks.LeibnizDerivation.toXRing r) z)))
      (diagAppLE_projOne f U a).symm
  · refine Eq.trans (congrArg (fun t => Ψ.hom (pushSection (pullback.diagonal f)
      (Stacks.Conormal.conormalSheaf (pullback.diagonal f))
      (Stacks.LeibnizDerivation.ambientChart f U)
      (Stacks.LeibnizDerivation.diagonal_preimage_ambientChart f U) t))
      (Stacks.LeibnizDerivation.kaehlerToConormal_d f V U hUV b)) ?_
    exact (hΨgen b).trans (hggen b).symm

/-- **[Stacks, Tag 08S2]: the canonical morphism `Ω_{X/S} ⟶ C_Δ` is an isomorphism**, for an
arbitrary morphism of schemes. This discharges the hypothesis
`IsIso (Stacks.LeibnizDerivation.toConormal f)` that both clauses of the tag were carried under
in `StacksDraft.AlgebraicGeometry.F3.LeibnizDerivation.Affine`. -/
instance isIso_toConormal : IsIso (Stacks.LeibnizDerivation.toConormal f) :=
  Stacks.LeibnizDerivation.isIso_toConormal_of_forall_isIso_kaehlerToConormal f
    fun _V U hUV hV hU => isIso_kaehlerToConormal f U hV hU hUV

/-! ### The two clauses of [Stacks, Tag 08S2], unconditionally -/

section Card

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 08S2].** The canonical isomorphism from the sheaf of relative differentials
of `X` over `S` to the conormal sheaf of its diagonal in `X ×_S X`.

This is `Stacks.LeibnizDerivation.diagonalConormalIso`, whose single hypothesis
`IsIso (Stacks.LeibnizDerivation.toConormal f)` is now discharged by `isIso_toConormal` and so
is carried by no argument here: `f` is an arbitrary morphism of schemes, and nothing is affine,
separated, Noetherian or quasi-compact. -/
@[stacks 08S2,
  ega "IV 16.3.1" "Ω¹_{X/S}=Gr₁(Δ_f)",
  sga "7 VI 5.5" "ordinary schemes",
  ega "IV 17.13.5"]
noncomputable def relativeDifferentialsIsoDiagonalConormal :
    Scheme.Hom.relativeDifferentials f ≅
      Stacks.Conormal.conormalSheaf (pullback.diagonal f) :=
  Stacks.LeibnizDerivation.diagonalConormalIso f

/-- **[Stacks, Tag 08S2], the canonical quotient formula.** The comparison isomorphism sends
`d b` to the image of `p₂^♯ b - p₁^♯ b` under the canonical quotient map from the ideal sheaf of
the diagonal to its conormal sheaf, on any open `V` of the coborder neighbourhood admitting the
tag's two containments.

This is `Stacks.LeibnizDerivation.diagonalConormalIso_hom_d_eq_quotientMap`, again with its
hypothesis discharged. -/
@[stacks 08S2 "canonical quotient formula"]
theorem relativeDifferentialsIsoDiagonalConormal_apply
    (V : (pullback.diagonal f).coborderRange.toScheme.Opens)
    (h₁ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.fst f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (h₂ : (pullback.diagonal f).coborderRange.ι ''ᵁ V ≤
      (pullback.snd f f) ⁻¹ᵁ ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (b : Γ(X, (pullback.diagonal f).liftCoborder ⁻¹ᵁ V))
    (x : (Stacks.ClosedImmersion.idealSheaf
      (pullback.diagonal f).liftCoborder.toLRSHom.toShHom).val.obj (.op V))
    (hx : (kernel.ι (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom
        (pullback.diagonal f).liftCoborder.toLRSHom.toShHom))).val.app (.op V) x =
      ((pullback.snd f f).appLE _ _ h₂).hom b - ((pullback.fst f f).appLE _ _ h₁).hom b) :
    ((relativeDifferentialsIsoDiagonalConormal f).hom.val.app
          (.op ((pullback.diagonal f).liftCoborder ⁻¹ᵁ V))).hom
        ((Scheme.Hom.universalRelativeDerivation f).d b) =
      (Stacks.Conormal.conormalQuotientMap (pullback.diagonal f)
        (pullback.diagonal f).coborderRange (pullback.diagonal f).liftCoborder
        (pullback.diagonal f).liftCoborder_ι).val.app (.op V) x :=
  Stacks.LeibnizDerivation.diagonalConormalIso_hom_d_eq_quotientMap f V h₁ h₂ b x hx

end Card

end Stacks.Tag08S2Assembly

end


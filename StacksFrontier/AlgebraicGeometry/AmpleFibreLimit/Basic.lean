module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleBridge.BaseChange
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleFibreNeighbourhood.RelativelyAmpleNeighbourhood
public import StacksFrontier.AlgebraicGeometry.AmpleLimit.Unconditional
public import StacksFrontier.AlgebraicGeometry.BlowupAmpleFamily.Noetherian
public import StacksFrontier.AlgebraicGeometry.Fibres.IdempotentExtensionApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.InvertibleUnconditional
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.RelativeAmpleBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.TensorPower
import all StacksFrontier.AlgebraicGeometry.Fibres.IdempotentExtensionApproximation

/-!
# Stacks Tag 0D2S: ampleness on one fibre of a proper morphism, with no Noetherian hypothesis

Let `f : X ⟶ Y` be a proper morphism of schemes, let `ℒ` be an invertible `𝒪_X`-module and let
`y ∈ Y` be a point at which `ℒ_y` is ample on the fibre `X_y`.  Then `y` has an open neighbourhood
`V ⊆ Y` such that `ℒ|_{f⁻¹V}` is ample relative to `f⁻¹V / V`.

Nothing is assumed on `Y`.  [Stacks, Tag 0D2N] is the same statement for a **Noetherian** base,
and this file removes that hypothesis by the limit argument of the source.

## Main results

* `Stacks.AmpleFibreLimit.exists_mem_isRelativelyAmple_of_isAmple_fibre`:
  **[Stacks, Tag 0D2S]**, carrying the attribute.
* `Stacks.AmpleFibreLimit.exists_mem_isRelativelyAmple_of_isAmple_fibre_of_qcqs`: the same over a
  quasi-compact quasi-separated base, which is where the limit argument runs.
* `Stacks.AmpleFibreLimit.isRelativelyAmple_pullbackModule_of_commSq`: relative ampleness pulls
  back along a commuting square whose two horizontal morphisms are affine — not only along a
  cartesian one.
* `Stacks.AmpleFibreLimit.isRelativelyAmple_morphismRestrict_preimage_of_commSq`: that statement
  read on the preimage of an open of the far base, which is the shape the limit argument ends in.
* `Stacks.AmpleFibreLimit.isAmple_fibre_morphismRestrict`: ampleness on a fibre is unchanged when
  the base is replaced by an open neighbourhood of the point.

## The route, which is the source's

The conclusion is local on the base (`isAmple_fibre_morphismRestrict` for the hypothesis and
`isRelativelyAmple_pullbackModule_of_commSq` for the conclusion), so the base may be taken affine
and in particular quasi-compact and quasi-separated.  Then:

1. [Stacks, Tag 0A0P], `AlgebraicGeometry.exists_isLimit_isProper_finiteType_arrow`, writes `f` as
   the inverse limit, in the arrow category, of proper morphisms `fⱼ : Xⱼ ⟶ Yⱼ` with every `Yⱼ` of
   finite type over `ℤ` — hence **Noetherian** — and every transition morphism affine on both
   sources and targets.  Its two component cones are limiting
   (`Stacks.AlgebraicGeometry.Fibres.isLimitLeftFuncMapCone` and its right-hand twin).
2. [Stacks, Tag 0B8W] (2),
   `Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit`, descends
   `ℒ` to an invertible module `ℒᵢ` on one `Xᵢ`.
3. The fibre of the limit is the limit of the fibres:
   `Stacks.AlgebraicGeometry.Fibres.fiberConeIsLimit`, whose own input is the residue field
   colimit [Stacks, Tag 0CUG].  The stages of that system of fibres are quasi-compact and
   quasi-separated because the `fⱼ` are proper and its transition morphisms are affine
   (`Stacks.AlgebraicGeometry.Fibres.isAffineHom_pullback_map`), so [Stacks, Tag 09MT] in the form
   `Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit_of_qcqs` descends
   ampleness of `ℒ_y` on `X_y` to ampleness on the fibre `X_{j, y_j}` of some later stage.
4. [Stacks, Tag 0D2N],
   `Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_isAmple_fibre`, applies **at
   that stage**, whose base is Noetherian, and produces an open `Vⱼ ∋ yⱼ` of `Yⱼ` over which
   `ℒⱼ|_{fⱼ⁻¹Vⱼ}` is relatively ample.
5. `V` is the inverse image of `Vⱼ` in `Y`.  The square with sides `X ⟶ Xⱼ`, `f`, `fⱼ` and
   `Y ⟶ Yⱼ` commutes but is **not** cartesian, and both its horizontal morphisms are affine, being
   projections of cofiltered limits with affine transition morphisms
   (`AlgebraicGeometry.isAffineHom_π_app'`).  That is exactly the input of
   `isRelativelyAmple_morphismRestrict_preimage_of_commSq`.

Step 5 is the step of the source that reads "`X ⟶ Y ×_{Yᵢ} Xᵢ` is affine, and the pullback of an
ample invertible sheaf by an affine morphism is ample".  Here it is factored as
[Stacks, Tag 0893] for the cartesian square
(`Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback`) followed by
[Stacks, Tag 0892] (2) for the affine morphism into the fibre product
(`Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom`); the morphism
into the fibre product is affine by cancellation, `AlgebraicGeometry.IsAffineHom.of_comp`, against
the projection, which is affine as a base change and separated because it is affine.

## Implementation notes

The limit machinery of step 1 and step 3 is not reproved here.  It is the machinery
`StacksFrontier/AlgebraicGeometry/Fibres/IdempotentExtensionApproximation.lean` built for
[Stacks, Tag 0G7X], whose reduction to the locally Noetherian base is the same limit argument with
an idempotent in place of ampleness.  Those declarations are `private` there, and this file reaches
them with `import all` rather than making them public (which would change base declarations) or
copying them (which would duplicate them); they occur only inside proofs here, never in a
statement or an exposed body.

**No field extension is descended along, and the reason is worth recording.**  The shorter route
to step 3 would be to base change the whole system to `Spec κ(y)` with
`AlgebraicGeometry.isLimitBaseChangeSystemCone`, which is already public and needs none of the
machinery of `Fibres/IdempotentExtensionApproximation.lean`.  **It does not work.**  That
statement base changes along a *fixed* `g : T ⟶ lim S`, so what [Stacks, Tag 09MT] then descends
is ampleness on `Xⱼ ×_{Yⱼ} Spec κ(y)` — not on the fibre
`X_{j, yⱼ} = Xⱼ ×_{Yⱼ} Spec κ(yⱼ)`, which is what [Stacks, Tag 0D2N] consumes.  Closing that gap
means descending ampleness of a *given* invertible module along the field extension
`κ(yⱼ) ⊆ κ(y)`, and the library's [Stacks, Tag 0BDC] is
`AlgebraicGeometry.exists_isAmple_of_fieldExtension`
(`StacksFrontier/AlgebraicGeometry/FieldExtensionDescent/Unconditional.lean`), whose conclusion is
the mere *existence* of an ample invertible module on the base and so drops the very module the
rest of the argument has to carry.  Taking the limit of the fibres themselves
(`Stacks.AlgebraicGeometry.Fibres.fiberConeIsLimit`, whose stages are the genuine fibres) avoids
the question outright, and that is why the machinery of that file is used here rather than the
shorter base-change route.

## References

* [Stacks Project, Tag 0D2S](https://stacks.math.columbia.edu/tag/0D2S)
* [Stacks Project, Tag 0D2N](https://stacks.math.columbia.edu/tag/0D2N)
* [Stacks Project, Tag 0A0P](https://stacks.math.columbia.edu/tag/0A0P)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 09MT](https://stacks.math.columbia.edu/tag/09MT)
* [Stacks Project, Tag 0CUG](https://stacks.math.columbia.edu/tag/0CUG)
* [Stacks Project, Tag 0893](https://stacks.math.columbia.edu/tag/0893)
* [Stacks Project, Tag 0892](https://stacks.math.columbia.edu/tag/0892)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open RingedSpaceModuleAdjunction
open Stacks.Ample (IsAmple IsInvertibleModule)
open Stacks.AmpleLocallyClosed (pullbackModule)
open Stacks.AlgebraicGeometry.Fibres
open Stacks.RelativeAmpleBaseChange (pullbackModuleCompIso pullbackModuleCongr)

universe u

namespace Stacks.AmpleFibreLimit

/-! ### Relative ampleness along an affine commuting square -/

/-- The isomorphism `a^* b^* L ≅ c^* d^* L` induced by a commuting square `a ≫ b = c ≫ d`. -/
private def pullbackModuleSquareIso {A B C D : Scheme.{u}} {a : A ⟶ B} {b : B ⟶ D} {c : A ⟶ C}
    {d : C ⟶ D} (h : a ≫ b = c ≫ d) (L : D.Modules) :
    pullbackModule a (pullbackModule b L) ≅ pullbackModule c (pullbackModule d L) :=
  (pullbackModuleCompIso a b L).symm ≪≫ pullbackModuleCongr h L ≪≫ pullbackModuleCompIso c d L

/-- **The lift into a fibre product of two affine morphisms is affine.**  If `t : X ⟶ X'` and
`b : S ⟶ S'` are affine and `t ≫ f' = f ≫ b`, then the induced `X ⟶ X' ×_{S'} S` is affine:
composed with the first projection it is `t`, and that projection is affine as a base change of
`b` and therefore separated, so `AlgebraicGeometry.IsAffineHom.of_comp` applies. -/
theorem isAffineHom_pullbackLift {X X' S S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (b : S ⟶ S') (t : X ⟶ X') (h : t ≫ f' = f ≫ b) [IsAffineHom t] [IsAffineHom b] :
    IsAffineHom (pullback.lift t f h) := by
  have : IsAffineHom (pullback.fst f' b) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (IsPullback.of_hasPullback f' b).flip inferInstance
  have : IsSeparated b := IsSeparated.of_isAffineHom b
  have : IsSeparated (pullback.fst f' b) := inferInstance
  have : IsAffineHom (pullback.lift t f h ≫ pullback.fst f' b) := by
    rw [pullback.lift_fst]
    infer_instance
  exact IsAffineHom.of_comp (pullback.lift t f h) (pullback.fst f' b)

/-- **Relative ampleness pulls back along a commuting square with affine horizontal morphisms.**
Let `t ≫ f' = f ≫ b` with `t : X ⟶ X'` and `b : S ⟶ S'` affine, and let `M` be an invertible
`𝒪_{X'}`-module ample relative to `f' : X' ⟶ S'`.  Then `t^* M` is ample relative to
`f : X ⟶ S`.

The square is not assumed cartesian.  It factors through the fibre product `X' ×_{S'} S`:
[Stacks, Tag 0893] makes the pullback of `M` there ample relative to the second projection, the
induced morphism `X ⟶ X' ×_{S'} S` is affine by
`Stacks.AmpleFibreLimit.isAffineHom_pullbackLift`, and [Stacks, Tag 0892] (2) in its relative form
`Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom` pulls relative
ampleness back along it. -/
theorem isRelativelyAmple_pullbackModule_of_commSq {X X' S S' : Scheme.{u}} (f : X ⟶ S)
    (f' : X' ⟶ S') (b : S ⟶ S') (t : X ⟶ X') (h : t ≫ f' = f ≫ b)
    [IsAffineHom b] [IsAffineHom t] (M : X'.Modules) [IsInvertibleModule X' M]
    (hM : Stacks.RelativeAmple.IsRelativelyAmple f' M) :
    Stacks.RelativeAmple.IsRelativelyAmple f (pullbackModule t M) := by
  have : IsAffineHom (pullback.lift t f h) := isAffineHom_pullbackLift f f' b t h
  have hcomp := Stacks.AmpleFibreNeighbourhood.isRelativelyAmple_pullbackModule_of_isAffineHom
    (pullback.lift t f h) (pullback.snd f' b) (pullbackModule (pullback.fst f' b) M)
    (Stacks.AmpleBridge.isRelativelyAmple_pullbackModule_of_isPullback
      (IsPullback.of_hasPullback f' b) M hM)
  rw [pullback.lift_snd] at hcomp
  refine (Stacks.RelativeVeryAmple.isRelativelyAmple_congr f _ _ ?_).mp hcomp
  exact (pullbackModuleCompIso (pullback.lift t f h) (pullback.fst f' b) M).symm
    ≪≫ pullbackModuleCongr (pullback.lift_fst t f h) M

/-- **The same statement read on the preimage of an open of the far base.**  Let
`t ≫ f' = f ≫ b` with `t` and `b` affine, let `V'` be an open of `S'` and suppose `M|_{f'⁻¹V'}` is
ample relative to `f' ∣_ V'`.  Then `(t^* M)|_{f⁻¹(b⁻¹V')}` is ample relative to
`f ∣_ (b⁻¹V')`.

The restricted square commutes over `V'`, its two horizontal morphisms being `b ∣_ V'`, a base
change of `b`, and the restriction of `t` to `t⁻¹(f'⁻¹V') = f⁻¹(b⁻¹V')`, which differs from the
base change `t ∣_ (f'⁻¹V')` by the isomorphism of two equal opens. -/
theorem isRelativelyAmple_morphismRestrict_preimage_of_commSq {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (b : S ⟶ S') (t : X ⟶ X') (h : t ≫ f' = f ≫ b)
    [IsAffineHom b] [IsAffineHom t] (V' : S'.Opens) (M : X'.Modules) [IsInvertibleModule X' M]
    (hM : Stacks.RelativeAmple.IsRelativelyAmple (f' ∣_ V')
      (pullbackModule (f' ⁻¹ᵁ V').ι M)) :
    Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ (b ⁻¹ᵁ V'))
      (pullbackModule (f ⁻¹ᵁ (b ⁻¹ᵁ V')).ι (pullbackModule t M)) := by
  have hpre : t ⁻¹ᵁ (f' ⁻¹ᵁ V') = f ⁻¹ᵁ (b ⁻¹ᵁ V') := by
    rw [← Scheme.Hom.comp_preimage, h, Scheme.Hom.comp_preimage]
  -- the restriction of `t` to the two preimages
  have : IsAffineHom (t ∣_ (f' ⁻¹ᵁ V')) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_morphismRestrict t (f' ⁻¹ᵁ V')).flip inferInstance
  have : IsIso (X.homOfLE hpre.ge) := inferInstanceAs (IsIso (X.isoOfEq hpre).inv)
  have hg : t.resLE (f' ⁻¹ᵁ V') (f ⁻¹ᵁ (b ⁻¹ᵁ V')) hpre.ge
      = X.homOfLE hpre.ge ≫ (t ∣_ (f' ⁻¹ᵁ V')) := by
    rw [← Scheme.Hom.resLE_eq_morphismRestrict, Scheme.Hom.map_resLE]
  have : IsAffineHom (t.resLE (f' ⁻¹ᵁ V') (f ⁻¹ᵁ (b ⁻¹ᵁ V')) hpre.ge) := by
    rw [hg]
    infer_instance
  have : IsAffineHom (b ∣_ V') :=
    MorphismProperty.of_isPullback (P := @IsAffineHom)
      (isPullback_morphismRestrict b V').flip inferInstance
  have hι : t.resLE (f' ⁻¹ᵁ V') (f ⁻¹ᵁ (b ⁻¹ᵁ V')) hpre.ge ≫ (f' ⁻¹ᵁ V').ι
      = (f ⁻¹ᵁ (b ⁻¹ᵁ V')).ι ≫ t := Scheme.Hom.resLE_comp_ι t hpre.ge
  -- the restricted square commutes
  have hsq : t.resLE (f' ⁻¹ᵁ V') (f ⁻¹ᵁ (b ⁻¹ᵁ V')) hpre.ge ≫ (f' ∣_ V')
      = (f ∣_ (b ⁻¹ᵁ V')) ≫ (b ∣_ V') := by
    refine (cancel_mono V'.ι).1 ?_
    have e₁ : (t.resLE (f' ⁻¹ᵁ V') (f ⁻¹ᵁ (b ⁻¹ᵁ V')) hpre.ge ≫ (f' ∣_ V')) ≫ V'.ι
        = (f ⁻¹ᵁ (b ⁻¹ᵁ V')).ι ≫ (f ≫ b) := by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hι, Category.assoc, h]
    have e₂ : ((f ∣_ (b ⁻¹ᵁ V')) ≫ (b ∣_ V')) ≫ V'.ι
        = (f ⁻¹ᵁ (b ⁻¹ᵁ V')).ι ≫ (f ≫ b) := by
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, morphismRestrict_ι,
        Category.assoc]
    rw [e₁, e₂]
  have hres := isRelativelyAmple_pullbackModule_of_commSq (f ∣_ (b ⁻¹ᵁ V')) (f' ∣_ V')
    (b ∣_ V') (t.resLE (f' ⁻¹ᵁ V') (f ⁻¹ᵁ (b ⁻¹ᵁ V')) hpre.ge) hsq
    (pullbackModule (f' ⁻¹ᵁ V').ι M) hM
  refine (Stacks.RelativeVeryAmple.isRelativelyAmple_congr (f ∣_ (b ⁻¹ᵁ V')) _ _ ?_).mp hres
  exact pullbackModuleSquareIso hι M

/-! ### Ampleness on a fibre is local on the base -/

/-- **Ampleness on a fibre only sees a neighbourhood of the point.**  For an open `A` of `S` and a
point `yA` of `A`, the fibre of `f ∣_ A` at `yA` is isomorphic to the fibre of `f` at the image of
`yA`, compatibly with the two inclusions into `X`, so ampleness of `ℒ` on the one is ampleness of
`ℒ|_{f⁻¹A}` on the other.

The comparison is cartesian by `AlgebraicGeometry.isPullback_fiberToSpecResidueField_of_isPullback`
applied to the restriction square, and is an isomorphism because an open immersion induces an
isomorphism of residue fields. -/
theorem isAmple_fibre_morphismRestrict {X S : Scheme.{u}} (f : X ⟶ S) (A : S.Opens)
    (L : X.Modules) [IsInvertibleModule X L] (yA : A.toScheme)
    (hL : IsAmple (f.fiber (A.ι yA)) (pullbackModule (f.fiberι (A.ι yA)) L)) :
    IsAmple ((f ∣_ A).fiber yA)
      (pullbackModule ((f ∣_ A).fiberι yA) (pullbackModule (f ⁻¹ᵁ A).ι L)) := by
  obtain ⟨k, hkiso, hkι⟩ : ∃ k : (f ∣_ A).fiber yA ⟶ f.fiber (A.ι yA), IsIso k ∧
      k ≫ f.fiberι (A.ι yA) = (f ∣_ A).fiberι yA ≫ (f ⁻¹ᵁ A).ι :=
    ⟨_, (isPullback_fiberToSpecResidueField_of_isPullback
      (isPullback_morphismRestrict f A).flip yA).isIso_fst_of_isIso,
      pullback.lift_fst _ _ _⟩
  have := hkiso
  have key := Stacks.AmpleBridge.isAmple_pullbackModule_of_isIso k
    (pullbackModule (f.fiberι (A.ι yA)) L) hL
  refine (Stacks.RelativeVeryAmple.isAmple_congr _ _ ?_).mp key
  exact pullbackModuleSquareIso hkι L

/-! ### The limit argument over a quasi-compact quasi-separated base -/

/-- The source of a proper morphism to a Noetherian scheme is quasi-compact. -/
private theorem compactSpace_of_isProper_of_isNoetherian {X Y : Scheme.{u}} (g : X ⟶ Y) [IsProper g]
    [hY : IsNoetherian Y] : CompactSpace X := by
  obtain ⟨-, huc, -⟩ := (isProper_iff g).mp ‹_›
  -- `QuasiCompact` follows from `UniversallyClosed` by the priority-900 instance of
  -- Mathlib's `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/UniversallyClosed.lean`; it is bound here rather than left to
  -- search, which does not reach through the chain at this project's instance-search depth.
  have hqc : QuasiCompact g := inferInstance
  exact @QuasiCompact.compactSpace_of_compactSpace _ _ g hqc hY.toCompactSpace

/-- The source of a proper morphism to a Noetherian scheme is quasi-separated. -/
private theorem quasiSeparatedSpace_of_isProper_of_isNoetherian {X Y : Scheme.{u}} (g : X ⟶ Y)
    [IsProper g] [hY : IsNoetherian Y] : QuasiSeparatedSpace X := by
  obtain ⟨-, -, hlft⟩ := (isProper_iff g).mp ‹_›
  have : IsLocallyNoetherian X :=
    @LocallyOfFiniteType.isLocallyNoetherian _ _ g hlft hY.toIsLocallyNoetherian
  infer_instance

/-- **[Stacks, Tag 0D2S] over a quasi-compact and quasi-separated base.**  This is where the
limit argument of the source runs; see the module documentation for the five steps. -/
theorem exists_mem_isRelativelyAmple_of_isAmple_fibre_of_qcqs {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] [CompactSpace S] [QuasiSeparatedSpace S] (L : X.Modules)
    [IsInvertibleModule X L] (y : S)
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L)) :
    ∃ V : S.Opens, y ∈ V ∧
      Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (pullbackModule (f ⁻¹ᵁ V).ι L) := by
  classical
  -- Invertibility of a pullback, [Stacks, Tag 0B8L], as a universally quantified helper rather
  -- than a sequence of pinned `haveI`s. The source scheme is left to be inferred from each use
  -- site, which is what makes it apply at the cone-vertex and stage spellings alike.
  have pbInv : ∀ {A B : Scheme.{u}} (g : A ⟶ B) (M : B.Modules) [IsInvertibleModule B M],
      IsInvertibleModule A (pullbackModule g M) := fun g M =>
    Stacks.RingedSpace.algebraicGeometryIsInvertible_modulePullback _ M
  -- **Step 1** ([Stacks, Tag 0A0P]): `f` as a limit of proper morphisms over Noetherian bases.
  obtain ⟨I, hI, hne, hdir, D, c, hproper, hftype, haff, ⟨hc⟩, ⟨iso⟩⟩ :=
    AlgebraicGeometry.exists_isLimit_isProper_finiteType_arrow f
  let := hI
  let := hne
  let := hdir
  have : IsCofilteredOrEmpty Iᵒᵖ := AlgebraicGeometry.isCofilteredOrEmpty_opposite_of_isDirected
  have : Nonempty Iᵒᵖ := Nonempty.map op hne
  have : IsCofiltered Iᵒᵖ := ⟨⟩
  have : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom ((D ⋙ Arrow.leftFunc).map g) :=
    fun g => (haff g).1
  have : ∀ {a b : Iᵒᵖ} (g : a ⟶ b), IsAffineHom ((D ⋙ Arrow.rightFunc).map g) :=
    fun g => (haff g).2
  -- the same limit, with the arrow `f` itself as its apex
  let c' : Cone D :=
    { pt := Arrow.mk f
      π :=
        { app := fun j => iso.inv ≫ c.π.app j
          naturality := fun a b g =>
            (Category.id_comp _).trans
              ((Category.assoc _ _ _).trans
                (congrArg (fun z => iso.inv ≫ z) (c.w g))).symm } }
  have hc' : IsLimit c' := hc.ofIsoLimit (Cone.ext iso fun j => by simp [c'])
  have hA : IsLimit (Arrow.leftFunc.mapCone c') := isLimitLeftFuncMapCone D c' hc'
  have hB : IsLimit (Arrow.rightFunc.mapCone c') := isLimitRightFuncMapCone D c' hc'
  have hpr : ∀ j, IsProper (D.obj j).hom := hproper
  -- every stage of the base system is Noetherian, being of finite type over `ℤ`
  have hNoe : ∀ j : Iᵒᵖ, IsNoetherian (D.obj j).right := fun j =>
    Stacks.BlowupAmpleFamily.isNoetherian_of_finiteType (D.obj j).right
      (hftype j).1 (hftype j).2
  have : ∀ j : Iᵒᵖ, CompactSpace ((D ⋙ Arrow.leftFunc).obj j) := fun j =>
    @compactSpace_of_isProper_of_isNoetherian _ _ (D.obj j).hom (hpr j) (hNoe j)
  have : ∀ j : Iᵒᵖ, QuasiSeparatedSpace ((D ⋙ Arrow.leftFunc).obj j) := fun j =>
    @quasiSeparatedSpace_of_isProper_of_isNoetherian _ _ (D.obj j).hom (hpr j) (hNoe j)
  -- **Step 2** ([Stacks, Tag 0B8W] (2)): `L` comes from a stage.
  have hLsheaf : AlgebraicGeometry.SheafOfModules.IsInvertible
      (Arrow.leftFunc.mapCone c').pt.sheaf.obj
      (Arrow.leftFunc.mapCone c').pt.ringCatSheaf.property L :=
    Stacks.AmpleBridge.isInvertible_ringedSpace L
  obtain ⟨i, Li, hLi, ⟨eL⟩⟩ :=
    Stacks.AlgebraicGeometry.ModuleLimits.exists_isInvertible_pullback_iso_of_isLimit
      (D ⋙ Arrow.leftFunc) (Arrow.leftFunc.mapCone c') hA L hLsheaf
  -- the invertibility of `Li` at **both** spellings of the stage: `stageIncl` lands in
  -- `(D ⋙ Arrow.leftFunc).obj i`, which instance search does not unify with `(D.obj i).left`
  have hLiInv : IsInvertibleModule ((D ⋙ Arrow.leftFunc).obj i) Li := hLi
  have : IsInvertibleModule (D.obj i).left Li := hLiInv
  -- **Step 3** ([Stacks, Tag 0CUG] and [Stacks, Tag 09MT]): ampleness on the fibre at a stage.
  let φ : (D ⋙ Arrow.leftFunc) ⟶ (D ⋙ Arrow.rightFunc) :=
    { app := fun j => (D.obj j).hom
      naturality := fun _ _ g => (D.map g).w }
  have hp : ∀ j, (Arrow.leftFunc.mapCone c').π.app j ≫ φ.app j =
      f ≫ (Arrow.rightFunc.mapCone c').π.app j := fun j => (c'.π.app j).w
  have hR := residueSpecConeIsLimit (D ⋙ Arrow.rightFunc) (Arrow.rightFunc.mapCone c') y hB
  have hFib := fiberConeIsLimit φ (Arrow.rightFunc.mapCone c') y
    (Arrow.leftFunc.mapCone c') f hp hA hB hR
  have : ∀ {a b : Iᵒᵖ} (g : a ⟶ b),
      IsAffineHom ((fiberDiagram φ (Arrow.rightFunc.mapCone c') y).map g) := fun g =>
    isAffineHom_pullback_map _ _ _ _ ((D ⋙ Arrow.leftFunc).map g)
      (Spec.map (residueTransition (D ⋙ Arrow.rightFunc) (Arrow.rightFunc.mapCone c') y g))
      ((D ⋙ Arrow.rightFunc).map g) (φ.naturality g).symm
      (specMap_residueTransition (D ⋙ Arrow.rightFunc) (Arrow.rightFunc.mapCone c') y g).symm
  have : ∀ j, CompactSpace ((fiberDiagram φ (Arrow.rightFunc.mapCone c') y).obj j) := fun j =>
    (quasiCompact_iff_compactSpace (pullback.snd (D.obj j).hom
      ((D.obj j).right.fromSpecResidueField ((c'.π.app j).right y)))).mp inferInstance
  have : ∀ j, QuasiSeparatedSpace ((fiberDiagram φ (Arrow.rightFunc.mapCone c') y).obj j) :=
    fun j => @quasiSeparatedSpace_of_quasiSeparated _ _ (pullback.snd (D.obj j).hom
      ((D.obj j).right.fromSpecResidueField ((c'.π.app j).right y))) inferInstance
      (MorphismProperty.of_isPullback (P := @QuasiSeparated)
        (IsPullback.of_hasPullback _ _) inferInstance)
  -- the hypothesis, read on the fibre of the limit as a module pulled back from the stage `i`
  have hample : AlgebraicGeometry.Scheme.Modules.IsAmple
      (fiberCone φ (Arrow.rightFunc.mapCone c') y (Arrow.leftFunc.mapCone c') f hp).pt
      (pullbackModule
        ((fiberCone φ (Arrow.rightFunc.mapCone c') y (Arrow.leftFunc.mapCone c') f hp).π.app i)
        (pullbackModule (stageIncl φ (Arrow.rightFunc.mapCone c') y i) Li)) := by
    -- The transport is done at `Stacks.Ample.IsAmple`, through
    -- `Stacks.RelativeVeryAmple.isAmple_congr`, rather than at
    -- `AlgebraicGeometry.Scheme.Modules.IsAmple` through `isAmple_of_iso`. The two are the same
    -- condition (`Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple`), but `isAmple_of_iso`
    -- asks for invertibility in the sheaf-level `SheafOfModules.IsInvertible` spelling, whose
    -- ring argument is `structureSheafRing`; reaching it from `IsInvertibleModule` would mean
    -- crossing two spellings of the structure ring sheaf. `isAmple_congr` asks only for
    -- `IsInvertibleModule`, so no crossing arises.
    -- `pbInv` gives the instance over the domain of the fibre inclusion, which is `f.fiber y`;
    -- the goal is stated over the cone vertex. The two are definitionally equal, and a `have`
    -- with an explicit type checks its term at default transparency, so the restatement is
    -- accepted there and the instance is then registered at the spelling the goal uses.
    -- Instance search itself cannot cross the two, the vertex being a projection of a `def`.
    have hinvLim : IsInvertibleModule
        (fiberCone φ (Arrow.rightFunc.mapCone c') y (Arrow.leftFunc.mapCone c') f hp).pt
        (pullbackModule (f.fiberι y) L) := pbInv (f.fiberι y) L
    have hinvTgt : IsInvertibleModule
        (fiberCone φ (Arrow.rightFunc.mapCone c') y (Arrow.leftFunc.mapCone c') f hp).pt
        (pullbackModule
          ((fiberCone φ (Arrow.rightFunc.mapCone c') y (Arrow.leftFunc.mapCone c') f hp).π.app i)
          (pullbackModule (stageIncl φ (Arrow.rightFunc.mapCone c') y i) Li)) := pbInv _ _
    refine (Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mpr ?_
    -- the two invertibility arguments are passed positionally rather than left to instance
    -- search, which cannot cross from the fibre spelling to the cone-vertex one
    refine (@Stacks.RelativeVeryAmple.isAmple_congr _ _ _ hinvLim hinvTgt ?_).mp hL
    refine ((Scheme.Modules.pullback (f.fiberι y)).mapIso eL) ≪≫ ?_
    exact pullbackModuleSquareIso
      (fiberConeMap_incl φ (Arrow.rightFunc.mapCone c') y
        (Arrow.leftFunc.mapCone c') f hp i).symm Li
  obtain ⟨j, hji, hampj⟩ :=
    Stacks.AlgebraicGeometry.AmpleLimit.exists_isAmple_pullback_map_of_isLimit_of_qcqs
      (fiberDiagram φ (Arrow.rightFunc.mapCone c') y)
      (fiberCone φ (Arrow.rightFunc.mapCone c') y (Arrow.leftFunc.mapCone c') f hp) hFib i
      (pullbackModule (stageIncl φ (Arrow.rightFunc.mapCone c') y i) Li) hample
  -- the module on the stage `j`, again at both spellings of the stage
  have hjInv : IsInvertibleModule ((D ⋙ Arrow.leftFunc).obj j)
      (pullbackModule ((D ⋙ Arrow.leftFunc).map hji) Li) := inferInstance
  have : IsInvertibleModule (D.obj j).left
      (pullbackModule ((D ⋙ Arrow.leftFunc).map hji) Li) := hjInv
  have hampStage : IsAmple ((D.obj j).hom.fiber ((c'.π.app j).right y))
      (pullbackModule ((D.obj j).hom.fiberι ((c'.π.app j).right y))
        (pullbackModule ((D ⋙ Arrow.leftFunc).map hji) Li)) := by
    -- the same move as on the limit side: transport at `Stacks.Ample.IsAmple`, where only
    -- `IsInvertibleModule` is asked for, instead of at the sheaf-level predicate whose ring
    -- argument is `structureSheafRing`.
    -- as on the limit side, both invertibility arguments are supplied positionally; the `have`s
    -- restate them over the stage fibre, which is the spelling this goal is written at.
    have hinvSrc : IsInvertibleModule ((D.obj j).hom.fiber ((c'.π.app j).right y))
        ((Scheme.Modules.pullback
            ((fiberDiagram φ (Arrow.rightFunc.mapCone c') y).map hji)).obj
          (pullbackModule (stageIncl φ (Arrow.rightFunc.mapCone c') y i) Li)) :=
      pbInv ((fiberDiagram φ (Arrow.rightFunc.mapCone c') y).map hji)
        (pullbackModule (stageIncl φ (Arrow.rightFunc.mapCone c') y i) Li)
    have hinvTgtS : IsInvertibleModule ((D.obj j).hom.fiber ((c'.π.app j).right y))
        (pullbackModule ((D.obj j).hom.fiberι ((c'.π.app j).right y))
          (pullbackModule ((D ⋙ Arrow.leftFunc).map hji) Li)) := pbInv _ _
    refine (@Stacks.RelativeVeryAmple.isAmple_congr _ _ _ hinvSrc hinvTgtS ?_).mp
      ((Stacks.PowerFamilyBridge.modulesIsAmple_iff_isAmple _ _).mp hampj)
    exact pullbackModuleSquareIso (stageMap_incl φ (Arrow.rightFunc.mapCone c') y hji) Li
  -- **Step 4** ([Stacks, Tag 0D2N] at the Noetherian stage).
  have := hNoe j
  have := hpr j
  obtain ⟨Vj, hyj, hRelj⟩ :=
    Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_isAmple_fibre
      (D.obj j).hom (pullbackModule ((D ⋙ Arrow.leftFunc).map hji) Li)
      ((c'.π.app j).right y) hampStage
  -- **Step 5**: pull the neighbourhood back along the affine projections of the limit.
  have : IsAffineHom ((c'.π.app j).left) :=
    AlgebraicGeometry.isAffineHom_π_app' (D ⋙ Arrow.leftFunc) (Arrow.leftFunc.mapCone c') hA j
  have : IsAffineHom ((c'.π.app j).right) :=
    AlgebraicGeometry.isAffineHom_π_app' (D ⋙ Arrow.rightFunc) (Arrow.rightFunc.mapCone c') hB j
  refine ⟨(c'.π.app j).right ⁻¹ᵁ Vj, hyj, ?_⟩
  have hfinal := isRelativelyAmple_morphismRestrict_preimage_of_commSq f (D.obj j).hom
    ((c'.π.app j).right) ((c'.π.app j).left) (c'.π.app j).w Vj
    (pullbackModule ((D ⋙ Arrow.leftFunc).map hji) Li) hRelj
  refine (Stacks.RelativeVeryAmple.isRelativelyAmple_congr _ _ _ ?_).mp hfinal
  -- the module pulled back from the stage `j` along the projection is `L` itself
  have hcone : (c'.π.app j).left ≫ (D ⋙ Arrow.leftFunc).map hji
      = (Arrow.leftFunc.mapCone c').π.app i := (Arrow.leftFunc.mapCone c').w hji
  exact (Scheme.Modules.pullback (f ⁻¹ᵁ ((c'.π.app j).right ⁻¹ᵁ Vj)).ι).mapIso
    ((pullbackModuleCompIso ((c'.π.app j).left) ((D ⋙ Arrow.leftFunc).map hji) Li).symm
      ≪≫ pullbackModuleCongr hcone Li ≪≫ eL.symm)

/-! ### Stacks Tag 0D2S -/

/-- **[Stacks, Tag 0D2S].**  Let `f : X ⟶ S` be a proper morphism of schemes, let `ℒ` be an
invertible `𝒪_X`-module and let `y` be a point of `S` such that `ℒ_y` is ample on the fibre `X_y`.
Then `y` has an open neighbourhood `V ⊆ S` such that `ℒ|_{f⁻¹V}` is ample relative to `f⁻¹V / V`.

**No hypothesis on `S`**:  this is [Stacks, Tag 0D2N],
`Stacks.AmpleFibreNeighbourhood.exists_mem_isRelativelyAmple_of_isAmple_fibre`, with its
Noetherian hypothesis removed by the limit argument described in the module documentation.  The
statement is otherwise the same, down to the spelling of the hypothesis and of the conclusion, and
invertibility of `ℒ_y` is an instance rather than a hypothesis for the same reason as there.

The base is replaced by an affine — hence quasi-compact and quasi-separated — open neighbourhood
`A` of `y`, which is legitimate in both directions: the hypothesis transfers by
`Stacks.AmpleFibreLimit.isAmple_fibre_morphismRestrict`, and the conclusion transfers back along
the isomorphism of arrows `AlgebraicGeometry.morphismRestrictRestrict` by
`Stacks.AmpleFibreLimit.isRelativelyAmple_pullbackModule_of_commSq`, whose two horizontal
morphisms are in this instance isomorphisms. -/
@[stacks 0D2S, ega "IV 9.6.4"]
theorem exists_mem_isRelativelyAmple_of_isAmple_fibre {X S : Scheme.{u}} (f : X ⟶ S)
    [IsProper f] (L : X.Modules) [IsInvertibleModule X L] (y : S)
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L)) :
    ∃ V : S.Opens, y ∈ V ∧
      Stacks.RelativeAmple.IsRelativelyAmple (f ∣_ V) (pullbackModule (f ⁻¹ᵁ V).ι L) := by
  classical
  obtain ⟨A, hA, hyA, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := S) (x := y) (U := ⊤) trivial
  have : IsAffine A.toScheme := hA
  have : IsProper (f ∣_ A) :=
    MorphismProperty.of_isPullback (P := @IsProper)
      (isPullback_morphismRestrict f A).flip inferInstance
  have hLA := isAmple_fibre_morphismRestrict f A L ⟨y, hyA⟩ hL
  obtain ⟨B, hyB, hRelB⟩ := exists_mem_isRelativelyAmple_of_isAmple_fibre_of_qcqs (f ∣_ A)
    (pullbackModule (f ⁻¹ᵁ A).ι L) ⟨y, hyA⟩ hLA
  refine ⟨A.ι ''ᵁ B, ⟨⟨y, hyA⟩, hyB, rfl⟩, ?_⟩
  -- the two restrictions agree up to an isomorphism of arrows
  let e : Arrow.mk (f ∣_ A ∣_ B) ≅ Arrow.mk (f ∣_ A.ι ''ᵁ B) := morphismRestrictRestrict f A B
  have hstage := isRelativelyAmple_pullbackModule_of_commSq (f ∣_ A.ι ''ᵁ B) (f ∣_ A ∣_ B)
    e.inv.right e.inv.left e.inv.w (pullbackModule ((f ∣_ A) ⁻¹ᵁ B).ι
      (pullbackModule (f ⁻¹ᵁ A).ι L)) hRelB
  refine (Stacks.RelativeVeryAmple.isRelativelyAmple_congr (f ∣_ A.ι ''ᵁ B) _ _ ?_).mp hstage
  have hcomp : (e.inv.left ≫ ((f ∣_ A) ⁻¹ᵁ B).ι) ≫ (f ⁻¹ᵁ A).ι
      = (f ⁻¹ᵁ A.ι ''ᵁ B).ι := by
    simp [e, AlgebraicGeometry.morphismRestrictRestrict]
  exact (pullbackModuleCompIso e.inv.left ((f ∣_ A) ⁻¹ᵁ B).ι _).symm
    ≪≫ (pullbackModuleCompIso (e.inv.left ≫ ((f ∣_ A) ⁻¹ᵁ B).ι) (f ⁻¹ᵁ A).ι L).symm
    ≪≫ pullbackModuleCongr hcomp L

end Stacks.AmpleFibreLimit

end

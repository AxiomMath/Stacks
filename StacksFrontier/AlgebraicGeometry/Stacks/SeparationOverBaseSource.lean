module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiDMComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBaseQuantifier
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationConstructionA
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase

/-!
# A separation property passes from the target of a 1-morphism to its source
(Stacks 050L, parts (1), (2), (4), (5), (6) and (7))

Stacks 050L has eight assertions: for each of the four separation conditions of Stacks 04YW, if
`f : 𝒳 ⟶ 𝒴` has it and `𝒴` has it over the base, then `𝒳` has it over the base (parts (1)–(4)),
and the same four statements with "over the base" read absolutely (parts (5)–(8)).

Parts (1), (2) and (4) are each one application of the corresponding composition lemma of
Stacks 050K: by Stacks 050D the property of `𝒳` over `S` is the property of its structure
morphism `AlgebraicGeometry.Stack.structureMorphism`, and
`AlgebraicGeometry.Stack.comp_structureMorphism` says that morphism is `f` followed by the
structure morphism of `𝒴`.

Parts (5), (6) and (7) are each one application of part (1), resp. part (2), resp. part (3), at
the terminal scheme. What has to be supplied is a 1-morphism
`viewOverIntegers 𝒳 ⟶ viewOverIntegers 𝒴` carrying the separation condition of `f`: the
hom-bijection `AlgebraicGeometry.Stack.algebraicStackConstructionHomEquiv` of Stacks 04X5 produces
the 1-morphism, and `AlgebraicGeometry.Stack.isDM_changeBase_iff`, resp.
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_changeBase_iff`, resp.
`AlgebraicGeometry.Stack.isProper_relativeDiagonal_changeBase`, carries the condition across.
`AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers` is
`AlgebraicGeometry.Stack.changeBaseAlgebraicStack` along `terminal.from S` on the nose, so the
source and target of that 1-morphism need no further identification.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.isDMOver_of_isDM`: **Stacks 050L**, part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDMOver_of_isQuasiDM`: **Stacks 050L**, part (2).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparatedOver_of_isQuasiSeparated`:
  **Stacks 050L**, part (4).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyDM_of_isDM`: **Stacks 050L**, part (5).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiDM_of_isQuasiDM`: **Stacks 050L**,
  part (6).
* `AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelySeparated_of_isSeparated`:
  **Stacks 050L**, part (7).

## Implementation notes

The four predicates of Stacks 050D are abbreviations applied to the structure morphism, so each
of parts (1), (2) and (4) is reached by a term-level `show … from` ascription and no bridge lemma
is needed; the rewrite along `AlgebraicGeometry.Stack.comp_structureMorphism` is the whole content
of each proof. Parts (5)–(8) are the same abbreviations at the terminal scheme, so parts (5), (6)
and (7) need no ascription at all.

Part (3) itself is `AlgebraicGeometry.Stack.isSeparatedOver_of_isSeparated`, in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteSource`, and part (8) is
`AlgebraicGeometry.Stack.AlgebraicStacks.isAbsolutelyQuasiSeparated_of_isQuasiSeparated`, in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteQuasiSeparated`; both are stated where the
change-of-base input each needs is available, so all eight assertions of Stacks 050L are proved.
The transfer of separatedness along Construction A runs through the condition of Stacks 04XB at
properness rather than through an every-étale-chart condition, which is why it is
`AlgebraicGeometry.Stack.isProper_relativeDiagonal_changeBase` and not
`AlgebraicGeometry.Stack.hasRelativeProperty_smooth_changeBaseHom_iff` that supplies part (7).

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 050L, part (1).** If `f : 𝒳 ⟶ 𝒴` is Deligne–Mumford and `𝒴` is Deligne–Mumford over
the base scheme `S`, then `𝒳` is Deligne–Mumford over `S`.

The structure morphism of `𝒳` is `f` followed by the structure morphism of `𝒴`
(`AlgebraicGeometry.Stack.comp_structureMorphism`), so this is the Deligne–Mumford case of
Stacks 050K. -/
@[stacks 050L "dm_over_s"]
theorem isDMOver_of_isDM (f : 𝒳 ⟶ 𝒴) (hY : Stack.IsDMOver B S hS 𝒴) (hf : Stack.IsDM B S hS f) :
    Stack.IsDMOver B S hS 𝒳 :=
  show Stack.IsDM B S hS (Stack.structureMorphism B S hS 𝒳) from
    Stack.comp_structureMorphism B S hS f ▸
      isDM_comp B S hS f (Stack.structureMorphism B S hS 𝒴) hf hY

/-- **Stacks 050L, part (2).** If `f : 𝒳 ⟶ 𝒴` is quasi-DM and `𝒴` is quasi-DM over the base
scheme `S`, then `𝒳` is quasi-DM over `S`.

The structure morphism of `𝒳` is `f` followed by the structure morphism of `𝒴`
(`AlgebraicGeometry.Stack.comp_structureMorphism`), so this is the quasi-DM case of
Stacks 050K. -/
@[stacks 050L "quasi_dm_over_s"]
theorem isQuasiDMOver_of_isQuasiDM (f : 𝒳 ⟶ 𝒴) (hY : Stack.IsQuasiDMOver B S hS 𝒴)
    (hf : IsQuasiDM B S hS f) :
    Stack.IsQuasiDMOver B S hS 𝒳 :=
  show IsQuasiDM B S hS (Stack.structureMorphism B S hS 𝒳) from
    Stack.comp_structureMorphism B S hS f ▸
      isQuasiDM_comp B S hS f (Stack.structureMorphism B S hS 𝒴) hf hY

/-- **Stacks 050L, part (4).** If `f : 𝒳 ⟶ 𝒴` is quasi-separated and `𝒴` is quasi-separated over
the base scheme `S`, then `𝒳` is quasi-separated over `S`.

The structure morphism of `𝒳` is `f` followed by the structure morphism of `𝒴`
(`AlgebraicGeometry.Stack.comp_structureMorphism`), so this is the quasi-separated case of
Stacks 050K. -/
@[stacks 050L "quasi_separated_over_s"]
theorem isQuasiSeparatedOver_of_isQuasiSeparated (f : 𝒳 ⟶ 𝒴)
    (hY : Stack.IsQuasiSeparatedOver B S hS 𝒴) (hf : IsQuasiSeparated B S hS f) :
    Stack.IsQuasiSeparatedOver B S hS 𝒳 :=
  show IsQuasiSeparated B S hS (Stack.structureMorphism B S hS 𝒳) from
    Stack.comp_structureMorphism B S hS f ▸
      isQuasiSeparated_comp B S hS f (Stack.structureMorphism B S hS 𝒴) hf hY

section Absolute

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- The 1-morphism of views over the terminal scheme assigned to `f` by the hom-bijection of
Stacks 04X5. -/
private noncomputable def viewHom (f : 𝒳 ⟶ 𝒴) :
    viewOverIntegers B S hS hZ 𝒳 ⟶ viewOverIntegers B S hS hZ 𝒴 :=
  Bicategory.InducedBicategory.mkHom
    (Stack.algebraicStackConstructionHomEquiv B S (⊤_ Scheme.{u}) hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒳 𝒴 f).val

/-- **Stacks 050L, part (5).** If `f : 𝒳 ⟶ 𝒴` is Deligne–Mumford and `𝒴` is Deligne–Mumford,
then `𝒳` is Deligne–Mumford.

Both absolute properties are the corresponding properties over the terminal scheme of the views
`AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers` of `𝒳` and `𝒴` there, and that view is
`AlgebraicGeometry.Stack.changeBaseAlgebraicStack` along `terminal.from S` on the nose. So this is
part (1) at the terminal scheme, applied to the 1-morphism of views that the hom-bijection of
Stacks 04X5 assigns to `f`, which is Deligne–Mumford by
`AlgebraicGeometry.Stack.isDM_changeBase_iff`. -/
@[stacks 050L "dm_absolute"]
theorem isAbsolutelyDM_of_isDM (f : 𝒳 ⟶ 𝒴) (hY : IsAbsolutelyDM B S hS hZ 𝒴)
    (hf : Stack.IsDM B S hS f) :
    IsAbsolutelyDM B S hS hZ 𝒳 :=
  isDMOver_of_isDM B (⊤_ Scheme.{u}) hZ
    (viewHom B S hS hZ f)
    hY
    ((Stack.isDM_changeBase_iff B S (⊤_ Scheme.{u}) hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) f).2 hf)

/-- **Stacks 050L, part (6).** If `f : 𝒳 ⟶ 𝒴` is quasi-DM and `𝒴` is quasi-DM, then `𝒳` is
quasi-DM.

Part (2) at the terminal scheme, applied to the 1-morphism of views that the hom-bijection of
Stacks 04X5 assigns to `f`, which is quasi-DM by
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDM_changeBase_iff`. That comparison is stated at
`AlgebraicGeometry.Stack.AlgebraicStacks.IsQuasiDMWithRepresentableDiagonal`, the reading which
carries the representability witness of the relative diagonal, so the hypothesis and the
conclusion are passed across
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM`. -/
@[stacks 050L "quasi_dm_absolute"]
theorem isAbsolutelyQuasiDM_of_isQuasiDM (f : 𝒳 ⟶ 𝒴) (hY : IsAbsolutelyQuasiDM B S hS hZ 𝒴)
    (hf : IsQuasiDM B S hS f) :
    IsAbsolutelyQuasiDM B S hS hZ 𝒳 :=
  isQuasiDMOver_of_isQuasiDM B (⊤_ Scheme.{u}) hZ
    (viewHom B S hS hZ f)
    hY
    ((isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B (⊤_ Scheme.{u}) hZ _).1
      ((isQuasiDM_changeBase_iff B S (⊤_ Scheme.{u}) hS hZ
        (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) f).2
        ((isQuasiDMWithRepresentableDiagonal_iff_isQuasiDM B S hS f).2 hf)))

/-- **Stacks 050L, part (7).** If `f : 𝒳 ⟶ 𝒴` is separated and `𝒴` is separated, then `𝒳` is
separated.

Both absolute properties are separatedness over the terminal scheme of the views
`AlgebraicGeometry.Stack.AlgebraicStacks.viewOverIntegers` of `𝒳` and `𝒴` there, and that view is
`AlgebraicGeometry.Stack.changeBaseAlgebraicStack` along `terminal.from S` on the nose. So this is
part (3) at the terminal scheme, applied to the 1-morphism of views that the hom-bijection of
Stacks 04X5 assigns to `f`, which is separated by
`AlgebraicGeometry.Stack.isProper_relativeDiagonal_changeBase`. -/
@[stacks 050L "separated_absolute"]
theorem isAbsolutelySeparated_of_isSeparated (f : 𝒳 ⟶ 𝒴)
    (hY : IsAbsolutelySeparated B S hS hZ 𝒴) (hf : IsSeparated B S hS f) :
    IsAbsolutelySeparated B S hS hZ 𝒳 :=
  Stack.isSeparatedOver_of_isSeparated B (⊤_ Scheme.{u}) hZ
    (viewHom B S hS hZ f)
    hY
    (Stack.isProper_relativeDiagonal_changeBase B S (⊤_ Scheme.{u}) hS hZ
      (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒳.val 𝒴.val f.hom hf)

end Absolute

end AlgebraicGeometry.Stack.AlgebraicStacks

end

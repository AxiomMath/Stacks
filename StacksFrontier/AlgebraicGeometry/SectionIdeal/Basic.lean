module

public import StacksFrontier.AlgebraicGeometry.SectionIdeal.Qcoh
public import StacksFrontier.AlgebraicGeometry.ZeroSchemeAnnihilation.Basic

/-!
# Stacks Tag 0C6K: the exact sequence of a regular section

For `L` an invertible `𝒪_X`-module, `s` a global section of `L` and `i : Z(s) ⟶ X` the inclusion
of its zero scheme, the restriction map `L ⟶ i_*(L|_{Z(s)})` **is** the cokernel of multiplication
by `s`; and when `s` is *regular* — Stacks Tag 01WY, monicity of that multiplication map — the
sequence

`0 ⟶ 𝒪_X ⟶ L ⟶ i_* (L|_{Z(s)}) ⟶ 0`

is short exact. Those two statements are the two assertions of Tag 0C6K's label
`regular_section_sequence`, and this file closes them.

## Main results

* `Stacks.Tag0C6KSectionIdeal.restrictionUnit_comp_eq_zero`: **a global section restricts to zero
  on its own zero scheme.** This is the hypothesis named `hz` in the general
  form of the label's two assertions.
* `Stacks.Tag0C6KSectionIdeal.exists_cokernelIso_zeroScheme` and
  `Stacks.Tag0C6KSectionIdeal.shortExact_zeroScheme`: **the two assertions of Tag 0C6K's label
  `regular_section_sequence`**, with no hypotheses beyond those of the tagged statement.

## How the hypothesis `hz` is discharged

The engine of both assertions, and the discharge of their other hypothesis `hiso` by Stacks
Tag 08KS, are in the library:

* `Stacks.RegularSectionSequence.exists_cokernelIso_restrictionUnit` and
  `Stacks.RegularSectionSequence.shortExact_restrictionUnit` prove both assertions for an arbitrary
  closed subscheme on the two hypotheses `hz` and `hiso`;
* `Stacks.Tag08KS.exists_cokernelIso_restrictionUnit_of_annihilated` replaces `hiso` by the
  annihilation condition of Tag 08KS;
* `Stacks.Tag0C6KZeroSchemeAnnihilation.exists_cokernelIso_zeroScheme` and `.shortExact_zeroScheme`
  discharge that annihilation condition at the zero scheme, leaving `hz` alone.

What `hz` needs is the *reverse* of the inclusion annihilation uses. The zero scheme is
`Scheme.IdealSheafData.ofIdeals` of the family `U ↦ span {φ (s|_U)}`, and
`Scheme.IdealSheafData.ideal_ofIdeals_le` gives only `ideal ≤ family` — enough to move a section of
the ideal into the span of `s`, which is annihilation, and useless for `hz`, which needs `s` itself
to lie in the ideal. The missing inclusion is Stacks Tag 02OQ's defining-ideal assertion, proved in
`Qcoh.lean` of this directory as `Stacks.Tag02OQSectionIdeal.zeroScheme_ideal`.

With it, `hz` is three steps. A morphism of sheaves of modules out of the structure sheaf is zero
exactly when the section it names is zero, that section is zero because it is locally zero, and on
an open where `L` is trivialised by `e` the section is `e (s|_V) • e⁻¹ 1` with `e (s|_V)` in the
ideal of the zero scheme — so it is killed by the one scalar that annihilates every pushforward
along `i`, the kernel ideal of `i^♯`. That last annihilation needs no new input either: a
pushforward is trivially in the essential image of the pushforward functor, and
`Stacks.Tag08KS.essImage_pushforward_iff_of_isClosedImmersion` reads membership of the essential
image as exactly that annihilation.

## Implementation notes

The trivialisation of an invertible module on a neighbourhood of a point — four lines from Stacks
Tag 0B8M, and used here to compute on an open where `L` is trivial — is
`Stacks.Tag0C6KZeroSchemeAnnihilation.exists_local_section_linearEquiv`, taken from
`StacksFrontier/AlgebraicGeometry/ZeroSchemeAnnihilation/Basic.lean`.

Everything is stated over `SheafOfModules.{u} X.ringCatSheaf` rather than over
`AlgebraicGeometry.Scheme.Modules`, because
the latter is a `def`, and `f ≫ g = 0` does not elaborate
through it because the hom type carries no `Zero` instance at that spelling.

## References

* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 01WY](https://stacks.math.columbia.edu/tag/01WY)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Tag0C6KSectionIdeal

/-
`Stacks.Tag0C6KSectionIdeal.exists_local_section_linearEquiv` lived here and repeated what is
now public as `Stacks.Tag0C6KZeroSchemeAnnihilation.exists_local_section_linearEquiv`:
`StacksFrontier/AlgebraicGeometry/ZeroSchemeAnnihilation/Basic.lean:127`, a file this one imports.
-/

/-- A morphism out of the structure sheaf is zero as soon as the section naming it is: the
converse of `Stacks.Tag0C6KZeroSchemeAnnihilation.app_eval_eq_zero_of_comp_eq_zero`. -/
theorem comp_eq_zero_of_app_eval_eq_zero {X : Scheme.{u}}
    {L M : SheafOfModules.{u} X.ringCatSheaf} (s : L.sections) (p : L ⟶ M)
    (hp : ∀ V : Opens X, p.val.app (op V) (s.eval (op V)) = 0) :
    L.unitHomEquiv.symm s ≫ p = 0 := by
  let z : M.sections := PresheafOfModules.sectionsMk (fun U => (0 : M.val.obj U)) (by
    intro U V h
    exact map_zero _)
  have hsz : SheafOfModules.sectionsMap p s = z := by
    apply PresheafOfModules.sections_ext
    exact fun U => hp U.unop
  have hzero : M.unitHomEquiv (0 : SheafOfModules.unit X.ringCatSheaf ⟶ M) = z := by
    apply PresheafOfModules.sections_ext
    exact fun _ => rfl
  apply M.unitHomEquiv.injective
  rw [SheafOfModules.unitHomEquiv_comp_apply, L.unitHomEquiv.apply_symm_apply, hsz, hzero]

/-- The image of a global section under a morphism of sheaves of modules vanishes over an open as
soon as it vanishes over a neighbourhood of each of its points, the target being a sheaf. -/
theorem app_eval_eq_zero_of_nhds {X : Scheme.{u}}
    {L M : SheafOfModules.{u} X.ringCatSheaf} (s : L.sections) (p : L ⟶ M) (V : Opens X)
    (h : ∀ x ∈ V, ∃ (V' : Opens X) (_ : V' ≤ V), x ∈ V' ∧
      p.val.app (op V') (s.eval (op V')) = 0) :
    p.val.app (op V) (s.eval (op V)) = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext (X := X.toTopCat) (A := AddCommGrpCat.{u})
    (F := M.val.presheaf) (U := op V) (s := p.val.app (op V) (s.eval (op V))) (t := 0) M.isSheaf
  intro x hx
  obtain ⟨V', hV'V, hxV', hvanish⟩ := h x hx
  refine ⟨V', hV'V, hxV', ?_⟩
  have hres : L.val.map (homOfLE hV'V).op (s.eval (op V)) = s.eval (op V') :=
    PresheafOfModules.sections_property s (homOfLE hV'V).op
  have hnat : p.val.app (op V') (L.val.map (homOfLE hV'V).op (s.eval (op V))) =
      M.val.map (homOfLE hV'V).op (p.val.app (op V) (s.eval (op V))) :=
    PresheafOfModules.naturality_apply p.val _ _
  have hzero : M.val.map (homOfLE hV'V).op (p.val.app (op V) (s.eval (op V))) = 0 := by
    rw [← hnat, hres]
    exact hvanish
  exact hzero.trans (map_zero _).symm

variable (X : Scheme.{u})

/-- The kernel ideal of `i^♯` annihilates the sections of any pushforward along the inclusion of a
closed subscheme: a pushforward lies in the essential image of the pushforward functor, and Stacks
Tag 08KS says membership of that essential image *is* this annihilation. -/
theorem ker_annihilates_pushforward (D : X.IdealSheafData)
    (N : SheafOfModules.{u} D.subscheme.ringCatSheaf) (V : Opens X)
    (a : X.ringCatSheaf.obj.obj (op V))
    (ha : a ∈ RingHom.ker (D.subschemeι.toLRSHom.c.app (op V)).hom)
    (m : ((SheafOfModules.pushforward.{u} D.subschemeι.toRingCatSheafHom).obj N).val.obj (op V)) :
    a • m = 0 :=
  (Stacks.Tag08KS.essImage_pushforward_iff_of_isClosedImmersion D.subschemeι
    ((SheafOfModules.pushforward.{u} D.subschemeι.toRingCatSheafHom).obj N)).mp
      (Functor.obj_mem_essImage _ N) V a ha m

/-- Multiplication by a global section of an invertible module, followed by restriction to the
section's own zero scheme, vanishes on every open: on a trivialising open the section is a multiple
of a generator by a function in the ideal of the zero scheme, and that function annihilates every
pushforward along the inclusion.

`L` is taken as an object of `AlgebraicGeometry.Scheme.Modules`, not of
`SheafOfModules.{u} X.ringCatSheaf`: the two are the same type, but `Γ(L, V)` carries its
`Module Γ(X, V)` instance only at the first spelling, and the local trivialisation and the ideal
computation both need it — the same split as in
`Stacks.Tag0C6KZeroSchemeAnnihilation.ker_annihilates`. -/
theorem restrictionUnit_app_eq_zero (L : X.Modules)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    (V : Opens X) :
    (Stacks.RegularSectionSequence.restrictionUnit
        (Stacks.RegularSectionSequence.zeroScheme X L (s.eval (op ⊤))) L).val.app (op V)
      (s.eval (op V)) = 0 := by
  refine app_eval_eq_zero_of_nhds s _ V fun x hx => ?_
  obtain ⟨W, hxW, hW⟩ :=
    Stacks.Tag0C6KZeroSchemeAnnihilation.exists_local_section_linearEquiv X L x
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hsub⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ V ⊓ W from ⟨hx, hxW⟩) (V ⊓ W).isOpen
  refine ⟨V', hsub.trans inf_le_left, hxV', ?_⟩
  obtain ⟨e⟩ := hW V' (hsub.trans inf_le_right)
  -- On a trivialising open the section is a multiple of the generator `e⁻¹ 1`.
  have hsplit : s.eval (op V') = e (s.eval (op V')) • e.symm 1 := by
    apply e.injective
    rw [map_smul, e.apply_symm_apply, smul_eq_mul, mul_one]
  -- Its coordinate lies in the ideal of the zero scheme, which is Stacks Tag 02OQ.
  have hmem : e (s.eval (op V')) ∈ RingHom.ker ((Stacks.RegularSectionSequence.zeroScheme X L
      (s.eval (op ⊤))).subschemeι.toLRSHom.c.app (op V')).hom := by
    show e (s.eval (op V')) ∈ RingHom.ker ((Stacks.RegularSectionSequence.zeroScheme X L
      (s.eval (op ⊤))).subschemeι.app V').hom
    rw [Scheme.IdealSheafData.ker_subschemeι_app _ ⟨V', hV'⟩,
      Stacks.Tag02OQSectionIdeal.zeroScheme_ideal L (s.eval (op ⊤)) ⟨V', hV'⟩]
    exact Ideal.subset_span ⟨e.toLinearMap,
      congrArg e (PresheafOfModules.sections_property s (homOfLE le_top).op).symm⟩
  rw [hsplit]
  exact (((Stacks.RegularSectionSequence.restrictionUnit
      (Stacks.RegularSectionSequence.zeroScheme X L (s.eval (op ⊤))) L).val.app
        (op V')).hom.map_smul _ _).trans
    (ker_annihilates_pushforward X _ _ V' _ hmem _)

/-- **A global section of an invertible module restricts to zero on its own zero scheme.** This is
the hypothesis `hz` of `Stacks.RegularSectionSequence.exists_cokernelIso_restrictionUnit` and of
`Stacks.Tag0C6KZeroSchemeAnnihilation.exists_cokernelIso_zeroScheme`, and the last one either
carried. -/
theorem restrictionUnit_comp_eq_zero (L : SheafOfModules.{u} X.ringCatSheaf)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections) :
    L.unitHomEquiv.symm s ≫ Stacks.RegularSectionSequence.restrictionUnit
      (Stacks.RegularSectionSequence.zeroScheme X L (s.eval (op ⊤))) L = 0 :=
  comp_eq_zero_of_app_eval_eq_zero s _ (restrictionUnit_app_eq_zero X L s)

/-- **The first assertion of Stacks Tag 0C6K's label `regular_section_sequence`.** For `L` an
invertible `𝒪_X`-module and `s` a global section of `L`, the restriction map
`L ⟶ i_* (L|_{Z(s)})` to the zero scheme of `s` *is* the cokernel of multiplication by `s`,
compatibly with the cokernel projection. No regularity of `s` is used, as in the source. -/
@[stacks 0C6K "regular_section_sequence"]
theorem exists_cokernelIso_zeroScheme (L : SheafOfModules.{u} X.ringCatSheaf)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections) :
    ∃ e : cokernel (L.unitHomEquiv.symm s) ≅
        (SheafOfModules.pushforward.{u} (Stacks.RegularSectionSequence.zeroScheme X L
            (s.eval (op ⊤))).subschemeι.toRingCatSheafHom).obj
          ((SheafOfModules.pullback.{u} (Stacks.RegularSectionSequence.zeroScheme X L
            (s.eval (op ⊤))).subschemeι.toRingCatSheafHom).obj L),
      cokernel.π (L.unitHomEquiv.symm s) ≫ e.hom =
        Stacks.RegularSectionSequence.restrictionUnit
          (Stacks.RegularSectionSequence.zeroScheme X L (s.eval (op ⊤))) L :=
  Stacks.Tag0C6KZeroSchemeAnnihilation.exists_cokernelIso_zeroScheme X L s
    (restrictionUnit_comp_eq_zero X L s)

/-- **The second assertion of Stacks Tag 0C6K's label `regular_section_sequence`.** For `s` a
*regular* global section of an invertible module — regularity being monicity of multiplication by
`s`, which is Stacks Tag 01WY and is literally the hypothesis below — the sequence
`0 ⟶ 𝒪_X ⟶ L ⟶ i_* (L|_{Z(s)}) ⟶ 0` is short exact. -/
@[stacks 0C6K "regular_section_sequence"]
theorem shortExact_zeroScheme (L : SheafOfModules.{u} X.ringCatSheaf)
    [SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] (s : L.sections)
    [Mono (L.unitHomEquiv.symm s)] :
    ∃ h : L.unitHomEquiv.symm s ≫ Stacks.RegularSectionSequence.restrictionUnit
        (Stacks.RegularSectionSequence.zeroScheme X L (s.eval (op ⊤))) L = 0,
      (ShortComplex.mk (L.unitHomEquiv.symm s)
        (Stacks.RegularSectionSequence.restrictionUnit
          (Stacks.RegularSectionSequence.zeroScheme X L (s.eval (op ⊤))) L) h).ShortExact :=
  Stacks.Tag0C6KZeroSchemeAnnihilation.shortExact_zeroScheme X L s
    (restrictionUnit_comp_eq_zero X L s)

end Stacks.Tag0C6KSectionIdeal

end

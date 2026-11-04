module

public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.SectionGenerator
public import StacksFrontier.AlgebraicGeometry.NormAmple.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.RingedSpace
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Nonvanishing

/-!
# The pullback of a local generator is a local generator

Let `f : X ⟶ Y` be a morphism of schemes and `L` a sheaf of `𝒪_Y`-modules with a section
generating it over an open `U` of `Y`. The unit of `f^* ⊣ f_*` carries that section to a section
of `f^*L` over `f⁻¹(U)`, and this file proves that it generates `f^*L` there, with the transition
unit of two such pullbacks the pullback of the transition unit upstairs.

This is the input that [Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY) needs for
its pullback--power clause: the transition units of `f^*𝒩` are the pullbacks of those of `𝒩`, so
a norm of degree `d` carries them to their `d`-th powers.

## Main definitions

* `Stacks.SheafOfModules.pullbackGenerator`: **the pullback of a generator**, a generator of
  `f^*L` over `f⁻¹(U)`.

## Main results

* `Stacks.SheafOfModules.bijective_smul_of_bijective_on_cover`: **generation is local on the
  open** — a section of `L` over `U` that generates on each member of an open cover of `U`
  generates over every open inside `U`.
* `Stacks.SheafOfModules.notMem_maximalIdeal_smul_top_pullbackUnit`: the germ of the pullback of
  a generator is nonvanishing at every point of `f⁻¹(U)`.
* `Stacks.SheafOfModules.pullbackGenerator_restrict`: the pullback of a generator commutes with
  restriction.
* `Stacks.SheafOfModules.generatorRatioUnit_pullbackGenerator`: **the transition unit of two
  pulled-back generators is the pullback of the transition unit.**

## Implementation notes

Generating is a statement about the sections over *every* smaller open, while the unit of the
adjunction has no description on sections at all, so the two are connected through the stalks and
then spread back out over `f⁻¹(U)`. The three steps are:

* the germ of a generator is nonvanishing — `notMem_maximalIdeal_smul_top_of_generator`;
* that survives the pullback, because the stalk of `f^*L` at `x` is
  `𝒪_{X,x} ⊗_{𝒪_{Y,f x}} L_{f x}` by [Stacks, Tag 0098] and the equivalence carries the germ of
  the pulled-back section to `1 ⊗ (germ of s)`, so the question reduces to the algebraic
  `mem_maximalIdeal_smul_iff_tmul`. **The stalk formula is unconditional here**:
  `Stacks.RingedSpace.pullbackStalkFormula` is a theorem, proved in
  `StacksFrontier/AlgebraicGeometry/PullbackTensor/StalkFormula.lean`. Module docstrings
  elsewhere in this repository that describe it, or Tag 01CD, as an open input predate that file;
* a nonvanishing germ gives generation on *some* neighbourhood
  (`exists_bijective_smul_of_germ_notMem_maximalIdeal_smul_top`), and
  `bijective_smul_of_bijective_on_cover` promotes that to generation over every open inside
  `f⁻¹(U)`.

`bijective_smul_of_bijective_on_cover` is the only part proved from scratch, and it mentions no
germ and no stalk: both halves are the sheaf condition over the cover `{V ⊓ W i}` of `V` —
injectivity because a section of the structure sheaf is determined by its restrictions,
surjectivity because the local preimages are unique, hence agree on overlaps, hence glue. Keeping
it germ-free matters: a ringed space carries two definitionally equal module structures on a
stalk, Mathlib's and `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, and a goal holding
  one while a rewrite holds
the other is not closed by `rw`. Everything below that does touch a stalk is phrased in the
`Stacks.SheafOfModules.TensorStalkRingedSpace` vocabulary — `ringStalk`, `grpStalk`, `grpGerm` —
  which is the one the
lemmas above are stated in, so no transport between the two is needed anywhere.

The restriction and semilinearity laws of the unit on sections are proved as
`Stacks.RingedSpace.pullbackUnit_restrict` and `Stacks.RingedSpace.pullbackUnit_smul`; neither is
re-derived.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction
open IsLocalRing (maximalIdeal)
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules

/-! ### Generation is local on the open -/

variable {X : RingedSpace.{u, u}}

/-- Restriction of sections composes, and the proof of `≤` it is taken along is irrelevant. -/
theorem map_homOfLE_map_homOfLE (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    {A B C : Opens X.carrier} (hBA : B ≤ A) (hCB : C ≤ B) (hCA : C ≤ A)
    (y : L.val.obj (op A)) :
    L.val.map (homOfLE hCB).op (L.val.map (homOfLE hBA).op y) =
      L.val.map (homOfLE hCA).op y :=
  (PresheafOfModules.map_comp_apply L.val (homOfLE hBA).op (homOfLE hCB).op y).symm.trans
    (PresheafOfModules.congr_map_apply L.val (Subsingleton.elim _ _) y)

/-- Restriction carries `c • t|_A` to `c|_B • t|_B`. -/
theorem map_homOfLE_smul_map_homOfLE (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    {U : Opens X.carrier} (t : L.val.obj (op U)) {A B : Opens X.carrier} (hBA : B ≤ A)
    (hA : A ≤ U) (hB : B ≤ U) (c : X.presheaf.obj (op A)) :
    L.val.map (homOfLE hBA).op (c • L.val.map (homOfLE hA).op t) =
      X.presheaf.map (homOfLE hBA).op c • L.val.map (homOfLE hB).op t :=
  (PresheafOfModules.map_smul L.val (homOfLE hBA).op c (L.val.map (homOfLE hA).op t)).trans
    (congrArg (fun z => X.presheaf.map (homOfLE hBA).op c • z)
      (map_homOfLE_map_homOfLE L hA hBA hB t))

/-- If `c • t|_A = y`, then restricting to `B ≤ A` gives `c|_B • t|_B = y|_B`. -/
private theorem restrict_smul_eq_of_smul_eq (L : _root_.SheafOfModules.{u} (structureSheafRing X))
    {U : Opens X.carrier} (t : L.val.obj (op U)) {A B : Opens X.carrier} (hBA : B ≤ A)
    (hA : A ≤ U) (hB : B ≤ U) (c : X.presheaf.obj (op A)) {y : L.val.obj (op A)}
    (h : c • L.val.map (homOfLE hA).op t = y) :
    X.presheaf.map (homOfLE hBA).op c • L.val.map (homOfLE hB).op t =
      L.val.map (homOfLE hBA).op y :=
  (map_homOfLE_smul_map_homOfLE L t hBA hA hB c).symm.trans
    (congrArg (L.val.map (homOfLE hBA).op) h)

/-- **Injectivity of generation is local on the open.** If multiplication against a section `t`
of `L` over `U` is injective on every open inside each member of an open cover of `U`, then it is
injective on every open inside `U`. -/
theorem injective_smul_of_injective_on_cover
    (L : _root_.SheafOfModules.{u} (structureSheafRing X)) {U : Opens X.carrier}
    (t : L.val.obj (op U)) {ι : Type*} (W : ι → Opens X.carrier) (hWU : ∀ i, W i ≤ U)
    (hcov : U ≤ ⨆ i, W i)
    (hinj : ∀ (i : ι) (V : Opens X.carrier) (hV : V ≤ W i),
      Function.Injective fun c : X.presheaf.obj (op V) =>
        c • L.val.map (homOfLE (hV.trans (hWU i))).op t)
    (V : Opens X.carrier) (hV : V ≤ U) :
    Function.Injective fun c : X.presheaf.obj (op V) =>
      c • L.val.map (homOfLE hV).op t := by
  intro c c' hcc
  refine TopCat.Presheaf.section_ext (C := CommRingCat.{u})
    ⟨X.presheaf, X.IsSheaf⟩ V c c' fun z hz => ?_
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov (hV hz))
  have hzi : z ∈ W i ⊓ V := ⟨hi, hz⟩
  have hWiV : W i ⊓ V ≤ W i := inf_le_left
  have key : X.presheaf.map (homOfLE (inf_le_right : W i ⊓ V ≤ V)).op c •
        L.val.map (homOfLE (hWiV.trans (hWU i))).op t =
      X.presheaf.map (homOfLE (inf_le_right : W i ⊓ V ≤ V)).op c' •
        L.val.map (homOfLE (hWiV.trans (hWU i))).op t :=
    (restrict_smul_eq_of_smul_eq L t inf_le_right hV (hWiV.trans (hWU i)) c hcc).trans
      (map_homOfLE_smul_map_homOfLE L t inf_le_right hV (hWiV.trans (hWU i)) c')
  rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_right : W i ⊓ V ≤ V)) z hzi c,
    ← X.presheaf.germ_res_apply (homOfLE (inf_le_right : W i ⊓ V ≤ V)) z hzi c',
    (hinj i (W i ⊓ V) hWiV) key]

/-- **Surjectivity of generation is local on the open.** If a section `t` of `L` over `U`
generates `L` on every open inside each member of an open cover of `U`, then every section of `L`
over an open inside `U` is a multiple of `t`. -/
theorem surjective_smul_of_bijective_on_cover
    (L : _root_.SheafOfModules.{u} (structureSheafRing X)) {U : Opens X.carrier}
    (t : L.val.obj (op U)) {ι : Type*} (W : ι → Opens X.carrier) (hWU : ∀ i, W i ≤ U)
    (hcov : U ≤ ⨆ i, W i)
    (hbij : ∀ (i : ι) (V : Opens X.carrier) (hV : V ≤ W i),
      Function.Bijective fun c : X.presheaf.obj (op V) =>
        c • L.val.map (homOfLE (hV.trans (hWU i))).op t)
    (V : Opens X.carrier) (hV : V ≤ U) :
    Function.Surjective fun c : X.presheaf.obj (op V) =>
      c • L.val.map (homOfLE hV).op t := by
  classical
  intro m
  have local_preimage : ∀ z : V, ∃ (i : ι) (hz : z.val ∈ W i ⊓ V)
      (c : X.presheaf.obj (op (W i ⊓ V))),
      c • L.val.map (homOfLE ((inf_le_left : W i ⊓ V ≤ W i).trans (hWU i))).op t =
        L.val.map (homOfLE (inf_le_right : W i ⊓ V ≤ V)).op m := by
    intro z
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hcov (hV z.property))
    obtain ⟨c, hc⟩ := (hbij i (W i ⊓ V) inf_le_left).surjective
      (L.val.map (homOfLE (inf_le_right : W i ⊓ V ≤ V)).op m)
    exact ⟨i, ⟨hi, z.property⟩, c, hc⟩
  choose idx hzi c hc using local_preimage
  set A : V → Opens X.carrier := fun z => W (idx z) ⊓ V
  have hAV : ∀ z : V, A z ≤ V := fun _ => inf_le_right
  have hcovA : V ≤ ⨆ z, A z := fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzi ⟨z, hz⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf A c := by
    intro z y
    have hzy : A z ⊓ A y ≤ W (idx z) := inf_le_left.trans inf_le_left
    have hzyV : A z ⊓ A y ≤ V := inf_le_left.trans (hAV z)
    refine (hbij (idx z) (A z ⊓ A y) hzy).injective ?_
    have hz : X.presheaf.map (Opens.infLELeft (A z) (A y)).op (c z) •
          L.val.map (homOfLE (hzy.trans (hWU (idx z)))).op t =
        L.val.map (homOfLE hzyV).op m :=
      (restrict_smul_eq_of_smul_eq L t (Opens.infLELeft (A z) (A y)).le
        ((inf_le_left : A z ≤ W (idx z)).trans (hWU (idx z))) (hzy.trans (hWU (idx z)))
        (c z) (hc z)).trans
        (map_homOfLE_map_homOfLE L (hAV z) (Opens.infLELeft (A z) (A y)).le hzyV m)
    have hy : X.presheaf.map (Opens.infLERight (A z) (A y)).op (c y) •
          L.val.map (homOfLE (hzy.trans (hWU (idx z)))).op t =
        L.val.map (homOfLE hzyV).op m :=
      (restrict_smul_eq_of_smul_eq L t (Opens.infLERight (A z) (A y)).le
        ((inf_le_left : A y ≤ W (idx y)).trans (hWU (idx y))) (hzy.trans (hWU (idx z)))
        (c y) (hc y)).trans
        (map_homOfLE_map_homOfLE L (hAV y) (Opens.infLERight (A z) (A y)).le hzyV m)
    exact hz.trans hy.symm
  obtain ⟨cV, hcV, -⟩ :=
    X.sheaf.existsUnique_gluing' A V (fun z => homOfLE (hAV z)) hcovA c hcompat
  refine ⟨cV, ?_⟩
  refine (show TopCat.Sheaf AddCommGrpCat.{u} X.carrier from
    ⟨L.val.presheaf, _root_.SheafOfModules.isSheaf L⟩).eq_of_locally_eq'
    A V (fun z => homOfLE (hAV z)) hcovA _ m fun z => ?_
  exact (map_homOfLE_smul_map_homOfLE L t (hAV z) hV
      ((inf_le_left : A z ≤ W (idx z)).trans (hWU (idx z))) cV).trans
    ((congrArg (fun r : X.presheaf.obj (op (A z)) =>
      r • L.val.map (homOfLE ((inf_le_left : A z ≤ W (idx z)).trans (hWU (idx z)))).op t)
      (hcV z)).trans (hc z))

/-- **Generation is local on the open.** If a section `t` of `L` over `U` generates `L` on every
open inside each member of an open cover of `U`, then it generates `L` on every open inside `U`.

Both halves are the sheaf condition over the cover `{V ⊓ W i}` of `V`. -/
theorem bijective_smul_of_bijective_on_cover
    (L : _root_.SheafOfModules.{u} (structureSheafRing X)) {U : Opens X.carrier}
    (t : L.val.obj (op U)) {ι : Type*} (W : ι → Opens X.carrier) (hWU : ∀ i, W i ≤ U)
    (hcov : U ≤ ⨆ i, W i)
    (hbij : ∀ (i : ι) (V : Opens X.carrier) (hV : V ≤ W i),
      Function.Bijective fun c : X.presheaf.obj (op V) =>
        c • L.val.map (homOfLE (hV.trans (hWU i))).op t)
    (V : Opens X.carrier) (hV : V ≤ U) :
    Function.Bijective fun c : X.presheaf.obj (op V) =>
      c • L.val.map (homOfLE hV).op t :=
  ⟨injective_smul_of_injective_on_cover L t W hWU hcov (fun i V hV => (hbij i V hV).1) V hV,
    surjective_smul_of_bijective_on_cover L t W hWU hcov hbij V hV⟩

/-! ### The germ of a pulled-back generator -/

variable {X Y : Scheme.{u}}

/-- **The germ of the pullback of a local generator is nonvanishing.**

The stalk of `f^*L` at `x` is `𝒪_{X,x} ⊗_{𝒪_{Y,f x}} L_{f x}` by Tag 0098, and that equivalence
carries the germ of the pulled-back section to `1 ⊗ (germ of s)`; `mem_maximalIdeal_smul_iff_tmul`
then reduces the claim to nonvanishing of the germ of `s` itself, which is
`notMem_maximalIdeal_smul_top_of_generator`. -/
theorem notMem_maximalIdeal_smul_top_pullbackUnit (f : X ⟶ Y)
    (L : _root_.SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y.toRingedSpace))
    (hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L)
    (U : Y.Opens) (s : GeneratorSections Y.toRingedSpace L U)
    (x : X.carrier) (hx : x ∈ f ⁻¹ᵁ U) :
    grpGerm X.toRingedSpace
        ((Stacks.RingedSpace.pullbackFunctor f.toLRSHom.toShHom).obj L).val x (f ⁻¹ᵁ U) hx
        (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom L (op U) s.val) ∉
      maximalIdeal (ringStalk X.toRingedSpace x) •
        (⊤ : Submodule (ringStalk X.toRingedSpace x)
          (grpStalk X.toRingedSpace
            ((Stacks.RingedSpace.pullbackFunctor f.toLRSHom.toShHom).obj L).val x)) := by
  have hxU : f.base x ∈ U := hx
  let _ : Algebra (ringStalk Y.toRingedSpace (f.base x)) (ringStalk X.toRingedSpace x) :=
    (f.toLRSHom.stalkMap x).hom.toAlgebra
  have _hlocal : IsLocalHom (algebraMap (ringStalk Y.toRingedSpace (f.base x))
      (ringStalk X.toRingedSpace x)) := f.toLRSHom.prop x
  obtain ⟨e, he⟩ := Stacks.RingedSpace.pullbackStalkFormula f.toLRSHom.toShHom L x
  have := hL
  intro hmem
  refine notMem_maximalIdeal_smul_top_of_generator L s (f.base x) hxU ?_
  refine (mem_maximalIdeal_smul_iff_tmul
    (A := ringStalk Y.toRingedSpace (f.base x)) (B := ringStalk X.toRingedSpace x)
    (M := grpStalk Y.toRingedSpace L.val (f.base x))
    (grpGerm Y.toRingedSpace L.val (f.base x) U hxU s.val)).mpr ?_
  -- `he U hxU s.val` and the goal name the same germ in two spellings of the ringed space, so
  -- the transport is done by `congrArg` on the membership rather than by `rw`
  refine Eq.mp (congrArg (fun y => y ∈ maximalIdeal (ringStalk X.toRingedSpace x) •
    (⊤ : Submodule (ringStalk X.toRingedSpace x) _)) (he U hxU s.val)) ?_
  exact (mem_ideal_smul_top_iff_of_linearEquiv
    (maximalIdeal (ringStalk X.toRingedSpace x)) e _).mp hmem

/-! ### The pullback of a generator -/

/-- **The pullback of a local generator.** The unit of `f^* ⊣ f_*` carries a generator of `L` over
`U` to a generator of `f^*L` over `f⁻¹(U)`. -/
noncomputable def pullbackGenerator (f : X ⟶ Y) (L : Y.Modules)
    (hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L)
    (U : Y.Opens) (s : GeneratorSections Y.toRingedSpace L U) :
    GeneratorSections X.toRingedSpace ((modulePullback f.toLRSHom.toShHom).obj L)
      (f ⁻¹ᵁ U) := by
  classical
  refine ⟨Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom L (op U) s.val, ?_⟩
  -- Tag 0B8L is stated at the `structureSheafRing` spelling of the structure sheaf; the two
  -- propositions are definitionally equal, so the instance is carried across by ascription.
  have hYinv : IsInvertible Y.toRingedSpace.sheaf.obj
      (structureSheafRing Y.toRingedSpace).property L := hL
  have hinv : IsInvertible X.presheaf (structureSheafRing X.toRingedSpace).property
      ((modulePullback f.toLRSHom.toShHom).obj L) :=
    Stacks.RingedSpace.isInvertible_modulePullback f.toLRSHom.toShHom L
  choose W hxW hWU hbij using fun z : (f ⁻¹ᵁ U : X.Opens) =>
    exists_bijective_smul_of_germ_notMem_maximalIdeal_smul_top
      ((modulePullback f.toLRSHom.toShHom).obj L)
      (Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom L (op U) s.val) z.val z.property
      (notMem_maximalIdeal_smul_top_pullbackUnit f L hL U s z.val z.property)
  exact bijective_smul_of_bijective_on_cover ((modulePullback f.toLRSHom.toShHom).obj L) _ W hWU
    (fun z hz => Opens.mem_iSup.2 ⟨⟨z, hz⟩, hxW ⟨z, hz⟩⟩) hbij

/-- The section underlying `pullbackGenerator f L hL U s` is the image of `s` under the unit of
`f^* ⊣ f_*`. -/
@[simp]
theorem pullbackGenerator_val (f : X ⟶ Y) (L : Y.Modules)
    (hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L)
    (U : Y.Opens) (s : GeneratorSections Y.toRingedSpace L U) :
    (pullbackGenerator f L hL U s).val =
      Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom L (op U) s.val :=
  rfl

/-- **The pullback of a generator commutes with restriction.** -/
theorem pullbackGenerator_restrict (f : X ⟶ Y) (L : Y.Modules)
    (hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L)
    {U V : Y.Opens} (h : V ≤ U) (s : GeneratorSections Y.toRingedSpace L U) :
    generatorRestrict ((modulePullback f.toLRSHom.toShHom).obj L)
        ((Opens.map f.base).map (homOfLE h)).le (pullbackGenerator f L hL U s) =
      pullbackGenerator f L hL V (generatorRestrict L h s) :=
  Subtype.ext
    (Stacks.RingedSpace.pullbackUnit_restrict f.toLRSHom.toShHom L (homOfLE h).op s.val)

/-- **The transition unit of two pulled-back generators is the pullback of the transition unit
upstairs.** -/
theorem generatorRatioUnit_pullbackGenerator (f : X ⟶ Y) (L : Y.Modules)
    (hL : IsInvertible Y.presheaf (structureSheafRing Y.toRingedSpace).property L)
    (U : Y.Opens) (s t : GeneratorSections Y.toRingedSpace L U) :
    generatorRatioUnit ((modulePullback f.toLRSHom.toShHom).obj L) (f ⁻¹ᵁ U)
        (pullbackGenerator f L hL U s) (pullbackGenerator f L hL U t) =
      Units.map (f.app U).hom.toMonoidHom (generatorRatioUnit L U s t) := by
  refine generatorRatioUnit_eq _ _ _ _ _ ?_
  show Stacks.RingedSpace.pullbackUnit f.toLRSHom.toShHom L (op U) t.val = _
  rw [generatorRatio_spec L U s t]
  exact Stacks.RingedSpace.pullbackUnit_smul f.toLRSHom.toShHom L (op U)
    (generatorRatio L U s t) s.val

end Stacks.SheafOfModules

end

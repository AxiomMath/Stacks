module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleTrivialization
public import StacksFrontier.AlgebraicGeometry.InvertiblePullbackFlat.SectionGenerator

/-!
# A generating section pairs to the unit section on the whole open

`StacksFrontier/AlgebraicGeometry/InvertiblePullbackFlat/SectionGenerator.lean` passes from a
generator of a stalk of an invertible sheaf of modules to a generator of the sections on a
neighbourhood, and pairs such a section to the unit section near each point
(`Stacks.SheafOfModules.exists_le_tensorPairing_eq_unitSection`). This file adds the converse
and the gluing of those local pairings over a whole open.

## Main results

All in the namespace `Stacks.SheafOfModules`.

* `Invertible.isUnit_linearEquiv_of_surjective_smul`: a generator has unit image under any
  identification of the module with the ring.
* `notMem_maximalIdeal_smul_top_of_exists_surjective_smul` and
  `notMem_maximalIdeal_smul_top_of_forall_bijective_smul`: a section generating the sections on
  a cofinal family of opens around a point generates the stalk there.
* `tensorPairing_left_injective_of_forall_germ_notMem_maximalIdeal_smul_top`:
  a section of `𝒩` pairing to the unit section with a given generating section of `ℒ` over an
  open is unique.
* `exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top`:
  **a section of `ℒ` generating at every point of an open pairs to the unit section there** — the
  local pairings of `exists_le_tensorPairing_eq_unitSection` glue, because by the previous result
  they agree on overlaps.

## Implementation notes

**A separate module.** These results use
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleTrivialization` (for its algebraic core
`Stacks.SheafOfModules.tmul_left_injective`), which `SectionGenerator.lean` does not import.
They live here so that the statements of that file elaborate exactly as before.

**The gluing is stated for a section over an open and no tag is attached.** The last two results
are, for a *global* section over its own nonvanishing open,
`Stacks.SheafOfModules.tensorPairing_left_injective` and
`Stacks.SheafOfModules.exists_tensorPairing_eq_one`, the latter carrying
`@[stacks 01CY "inverse section"]`. They are generalised here off global sections, exactly as
`Stacks.SheafOfModules.isOpen_generatingLocus` generalises the openness clause of the same tag,
and the tag is withheld for the same reason recorded there: the clause of the tag is already covered
by the global statement.

**A composite restriction cannot appear in the `ℒ` slot of a `rw` motive.**
`tensorPairing_res_eq_unitSection_of_map_eq` takes the restricted section as a *variable* `a`
together with the equation identifying `a|_{W'}` with `t|_{W'}`, rather than taking the composite
`L.val.map i (L.val.map j t)` directly: the composite's declared type is a
`ModuleCat.restrictScalars`, so a goal mentioning it is not type-correct at `implicit`
transparency and every `rw` on it fails.

## References

* [Stacks Project, Tag 0BD7](https://stacks.math.columbia.edu/tag/0BD7)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open CategoryTheory TensorProduct Opposite TopologicalSpace AlgebraicGeometry IsLocalRing
open Stacks.SheafOfModules.TensorStalkRingedSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}} [∀ x : X.carrier, IsLocalRing (ringStalk X x)]
  {L N : SheafOfModules.{u} (structureSheafRing X)}

/-! ### A generator has unit image under a frame -/

namespace Invertible

/-- **A generator has unit image under any frame.** If multiplication by `c` is onto `M` and
`e : M ≃ₗ[R] R` is any identification of `M` with `R`, then `e c` is a unit: the preimage of
`e.symm 1` is an inverse.

This is the step `Stacks.Divisors.bijective_smul_of_span_eq_top` and the stalk-basis arguments
perform inline, and it is what identifies the scalar comparing two generators as a unit when one
of them is normalised to `1` by the frame — the shape the chart computation of [Stacks, Tag 0B3V]
clause 3 meets, where the frame is `eL` and `eL (q s) = 1`. It needs only surjectivity over the
one open, so it does not go through
`Stacks.SheafOfModules.isUnit_of_smul_eq_generator`, which asks both sections to generate on
every smaller open as well. -/
theorem isUnit_linearEquiv_of_surjective_smul {R : Type u} [CommRing R] {M : Type u}
    [AddCommGroup M] [Module R M] (e : M ≃ₗ[R] R) {c : M}
    (hc : Function.Surjective fun g : R => g • c) :
    IsUnit (e c) := by
  obtain ⟨g, hg⟩ := hc (e.symm 1)
  replace hg : g • c = e.symm 1 := hg
  have h : g * e c = 1 := by
    have h1 : e (g • c) = 1 := (congrArg e hg).trans (e.apply_symm_apply 1)
    rwa [map_smul, smul_eq_mul] at h1
  exact IsUnit.of_mul_eq_one g ((mul_comm (e c) g).trans h)

end Invertible

/-- The germ of a restricted section is the germ of the section. -/
private theorem grpGerm_restrictₛₗ {Y : RingedSpace.{u, u}}
    {M : SheafOfModules.{u} (structureSheafRing Y)} {U V : Opens Y.carrier} (h : V ≤ U)
    (y : Y.carrier) (hy : y ∈ V) (t : M.val.obj (op U)) :
    grpGerm Y M.val y V hy (M.val.restrictₛₗ (homOfLE h).op t) = grpGerm Y M.val y U (h hy) t :=
  TopCat.Presheaf.germ_res_apply (C := AddCommGrpCat.{u}) M.val.presheaf (homOfLE h) y hy t

/-! ### The converse: generating the sections forces the germ condition -/

variable (L) in
/-- **A section generating the sections on a cofinal family of opens around a point generates the
stalk there.** Let `t` be a section of an invertible `ℒ` over `U` and let `y ∈ U`. Suppose that
every open `V` containing `y` admits a smaller open `V' ⊆ V ∩ U`, still containing `y`, on which
every section of `ℒ` is a function times `t|_{V'}`. Then the germ of `t` at `y` does not lie in
`𝔪_y ℒ_y`.

This is the converse of
`Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top`, and it is
stated against a *cofinal* family rather than against every `V ≤ U` because that is the form a
trivialisation of a restriction supplies: the opens on which the trivialisation speaks are the
images `j(V')` of the opens of the subscheme, and those are cofinal in `U` without being all of
its opens.

The proof is the argument inside
`Stacks.ProjectiveBundleConormal.notMem_maximalSmul_germ_of_span_eq_top` with the affineness
removed. There the passage from sections to the stalk needs quasi-coherence, because generation is
known only over the one affine open; here generation is known on arbitrarily small opens, so the
section of `ℒ` whose germ escapes `𝔪_y ℒ_y` — produced by
`Stacks.SheafOfModules.exists_tensorPairing_eq_unitSection` from invertibility alone — is itself a
multiple of `t` near `y`, and `Submodule.smul_mem` does the rest. No affineness, no
quasi-coherence, and no properness statement about `𝔪_y ℒ_y`. -/
theorem notMem_maximalIdeal_smul_top_of_exists_surjective_smul
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    {U : Opens X.carrier} (t : L.val.obj (op U)) (y : X.carrier) (hy : y ∈ U)
    (hsurj : ∀ V : Opens X.carrier, y ∈ V →
      ∃ (V' : Opens X.carrier) (_ : y ∈ V') (_ : V' ≤ V) (hV'U : V' ≤ U),
        Function.Surjective fun c : X.presheaf.obj (op V') =>
          c • L.val.restrictₛₗ (homOfLE hV'U).op t) :
    grpGerm X L.val y U hy t ∉
      maximalIdeal (ringStalk X y) • (⊤ : Submodule (ringStalk X y) (grpStalk X L.val y)) := by
  obtain ⟨N, ⟨ψ⟩⟩ := (isInvertible_iff_exists_tensor_iso_unit
    (O := X.presheaf) (hO := (structureSheafRing X).property) L).mp ‹_›
  obtain ⟨W, hyW, a, b, hab⟩ := exists_tensorPairing_eq_unitSection ψ y
  have hna : grpGerm X L.val y W hyW a ∉
      maximalIdeal (ringStalk X y) • (⊤ : Submodule (ringStalk X y) (grpStalk X L.val y)) :=
    notMem_smul_of_tmul_eq_one (stalkPairing ψ y) _ (grpGerm X N.val y W hyW b)
      (bijective_smul_germ_of_tensorPairing_eq_unitSection ψ a b hab y hyW).1
  obtain ⟨V', hyV', hV'W, hV'U, hsur⟩ := hsurj W hyW
  obtain ⟨c, hc⟩ := hsur (L.val.restrictₛₗ (homOfLE hV'W).op a)
  replace hc : c • L.val.restrictₛₗ (homOfLE hV'U).op t
      = L.val.restrictₛₗ (homOfLE hV'W).op a := hc
  intro hmem
  refine hna ?_
  have key : grpGerm X L.val y W hyW a
      = ringGerm X y V' hyV' c • grpGerm X L.val y U hy t :=
    (grpGerm_restrictₛₗ hV'W y hyV' a).symm.trans
      ((congrArg (grpGerm X L.val y V' hyV') hc).symm.trans
        ((stalkModule_germ_smul X L.val y V' hyV' c _).trans
          (congrArg (fun z => ringGerm X y V' hyV' c • z) (grpGerm_restrictₛₗ hV'U y hyV' t))))
  exact key ▸ Submodule.smul_mem _ _ hmem

variable (L) in
/-- **A section generating the sections over every smaller open generates every stalk.** The
`V' = V ⊓ U` case of
`Stacks.SheafOfModules.notMem_maximalIdeal_smul_top_of_exists_surjective_smul`, and the exact
converse of `Stacks.SheafOfModules.bijective_smul_of_forall_germ_notMem_maximalIdeal_smul_top`:
for an invertible `ℒ` on a ringed space with local stalks, a section trivialising `ℒ` on `U` in
the sense of `Stacks.SheafOfModules.GeneratorSections` has, at every point of `U`, a germ
escaping `𝔪_y ℒ_y`. -/
theorem notMem_maximalIdeal_smul_top_of_forall_bijective_smul
    [IsInvertible X.presheaf (structureSheafRing X).property L]
    {U : Opens X.carrier} (t : L.val.obj (op U))
    (hbij : ∀ (V : Opens X.carrier) (hVU : V ≤ U),
      Function.Bijective fun c : X.presheaf.obj (op V) =>
        c • L.val.restrictₛₗ (homOfLE hVU).op t)
    (y : X.carrier) (hy : y ∈ U) :
    grpGerm X L.val y U hy t ∉
      maximalIdeal (ringStalk X y) • (⊤ : Submodule (ringStalk X y) (grpStalk X L.val y)) :=
  notMem_maximalIdeal_smul_top_of_exists_surjective_smul L t y hy fun V hyV =>
    ⟨V ⊓ U, ⟨hyV, hy⟩, inf_le_left, inf_le_right,
      (hbij (V ⊓ U) inf_le_right).surjective⟩

/-! ### The pairing on the whole of an open where the section generates -/

section Glue

variable (ψ : (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨(X).presheaf, (X).IsSheaf⟩).obj (L)).obj
    (N)) ≅ SheafOfModules.unit (structureSheafRing X))

omit [∀ x : X.carrier, IsLocalRing (ringStalk X x)] in
/-- **Restricting a pairing with the unit section.** If `a ∈ ℒ(W)` pairs with `b ∈ 𝒩(W)` to the
unit section and `a|_{W'}` is the restriction of `t ∈ ℒ(V)`, then `t|_{W'}` pairs with `b|_{W'}`
to the unit section.

The section over `W` is a variable `a` with an equation identifying its restriction, rather than
the composite restriction of `t`, for the transparency reason in the implementation notes. -/
theorem tensorPairing_res_eq_unitSection_of_map_eq
    {V W W' : Opens X.carrier} (hW'W : W' ≤ W) (hW'V : W' ≤ V)
    {t : L.val.obj (op V)} {a : L.val.obj (op W)} (b : N.val.obj (op W))
    (hat : L.val.map (homOfLE hW'W).op a = L.val.map (homOfLE hW'V).op t)
    (hb : tensorPairing ψ W a b = unitSection X W) :
    tensorPairing ψ W' (L.val.map (homOfLE hW'V).op t) (N.val.map (homOfLE hW'W).op b)
      = unitSection X W' := by
  rw [← hat, ← tensorPairing_res, hb]
  exact map_one ((structureSheafRing X).obj.map (homOfLE hW'W).op).hom

/-- **A section of `𝒩` pairing to the unit section with a generating section of `ℒ` is unique.**
Let `t` be a section of `ℒ` over `V` whose germ generates at every point of `V`. Then two
sections of `𝒩` over `V` with the same pairing against `t` are equal.

At each point the germ of `t` pairs to `1` with some germ of `𝒩`
(`Stacks.SheafOfModules.exists_le_tensorPairing_eq_unitSection`), so
`Stacks.SheafOfModules.tmul_left_injective` makes tensoring with the germ of `t` injective on the
stalk of `𝒩`; the two sections then have equal germs everywhere on `V`.

This is `Stacks.SheafOfModules.tensorPairing_left_injective` for a section defined on an open
rather than a global section on its nonvanishing open. -/
theorem tensorPairing_left_injective_of_forall_germ_notMem_maximalIdeal_smul_top
    (V : Opens X.carrier) (t : L.val.obj (op V))
    (ht : ∀ (y : X.carrier) (hy : y ∈ V), grpGerm X L.val y V hy t ∉
      maximalIdeal (ringStalk X y) • (⊤ : Submodule (ringStalk X y) (grpStalk X L.val y)))
    {b₁ b₂ : N.val.obj (op V)}
    (hb : tensorPairing ψ V t b₁ = tensorPairing ψ V t b₂) :
    b₁ = b₂ := by
  refine TopCat.Presheaf.section_ext
    ((SheafOfModules.toSheaf (structureSheafRing X)).obj N) V b₁ b₂ ?_
  intro z hzV
  obtain ⟨W, hzW, hWV, n, hn⟩ := exists_le_tensorPairing_eq_unitSection ψ t z hzV (ht z hzV)
  have hn' : tensorPairing ψ W (L.val.restrictₛₗ (homOfLE hWV).op t) n = unitSection X W := hn
  have h0 : stalkPairing ψ z
      (grpGerm X L.val z W hzW (L.val.restrictₛₗ (homOfLE hWV).op t) ⊗ₜ[ringStalk X z]
        grpGerm X N.val z W hzW n) = 1 :=
    (stalkPairing_germ ψ z W hzW (L.val.restrictₛₗ (homOfLE hWV).op t) n).trans
      (by rw [hn']; exact map_one (ringGerm X z W hzW))
  have h1 : stalkPairing ψ z
      (grpGerm X L.val z V hzV t ⊗ₜ[ringStalk X z] grpGerm X N.val z W hzW n) = 1 :=
    grpGerm_restrictₛₗ hWV z hzW t ▸ h0
  have hg : grpGerm X L.val z V hzV t ⊗ₜ[ringStalk X z] grpGerm X N.val z V hzV b₁
      = grpGerm X L.val z V hzV t ⊗ₜ[ringStalk X z] grpGerm X N.val z V hzV b₂ := by
    refine (stalkPairing ψ z).injective ?_
    rw [stalkPairing_germ, stalkPairing_germ, hb]
  exact tmul_left_injective (stalkPairing ψ z) h1 (grpStalk X N.val z) hg

/-- **A section generating at every point of an open pairs to the unit section over the whole of
it.** Let `ψ : ℒ ⊗_{𝒪_X} 𝒩 ≅ 𝒪_X` be a trivialization and let `t` be a section of `ℒ` over an
open `V` whose germ at every point of `V` does not lie in `𝔪_y ℒ_y`. Then there is a section `b`
of `𝒩` over `V` with `ψ (t ⊗ b) = 1`.

`Stacks.SheafOfModules.exists_le_tensorPairing_eq_unitSection` supplies such a `b` on a
neighbourhood of each point of `V`; the local sections agree on overlaps by
`tensorPairing_left_injective_of_forall_germ_notMem_maximalIdeal_smul_top`, so they glue, and the
pairing of the glued section with `t` agrees with the unit section locally, hence everywhere.

This is `Stacks.SheafOfModules.exists_tensorPairing_eq_one` for a section defined on an open
rather than a global section on its nonvanishing open; the tag of that statement is withheld
here, see the implementation notes. -/
theorem exists_tensorPairing_eq_one_of_forall_germ_notMem_maximalIdeal_smul_top
    (V : Opens X.carrier) (t : L.val.obj (op V))
    (ht : ∀ (y : X.carrier) (hy : y ∈ V), grpGerm X L.val y V hy t ∉
      maximalIdeal (ringStalk X y) • (⊤ : Submodule (ringStalk X y) (grpStalk X L.val y))) :
    ∃ b : N.val.obj (op V), tensorPairing ψ V t b = unitSection X V := by
  classical
  have hpt : ∀ z : {y : X.carrier // y ∈ V},
      ∃ (W : Opens X.carrier) (_ : z.1 ∈ W) (hWV : W ≤ V) (b : N.val.obj (op W)),
        tensorPairing ψ W (L.val.map (homOfLE hWV).op t) b = unitSection X W :=
    fun z => exists_le_tensorPairing_eq_unitSection ψ t z.1 z.2 (ht z.1 z.2)
  choose W hzW hWV b hb using hpt
  have hcover : V ≤ iSup W := fun y hy => Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hzW ⟨y, hy⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible
      ((SheafOfModules.toSheaf (structureSheafRing X)).obj N).1 W b := by
    intro i j
    have hle : W i ⊓ W j ≤ V := le_trans inf_le_left (hWV i)
    have hgerm : ∀ (y : X.carrier) (hy : y ∈ W i ⊓ W j),
        grpGerm X L.val y (W i ⊓ W j) hy (L.val.restrictₛₗ (homOfLE hle).op t) ∉
          maximalIdeal (ringStalk X y) •
            (⊤ : Submodule (ringStalk X y) (grpStalk X L.val y)) := by
      intro y hy
      exact (grpGerm_restrictₛₗ hle y hy t) ▸ ht y (hle hy)
    have hres : ∀ (k : {y : X.carrier // y ∈ V}) (hk : W i ⊓ W j ≤ W k),
        L.val.map (homOfLE hk).op (L.val.map (homOfLE (hWV k)).op t)
          = L.val.map (homOfLE hle).op t := by
      intro k hk
      rw [← L.val.map_comp_apply]
      congr 1
    have h1 := tensorPairing_res_eq_unitSection_of_map_eq ψ
      (inf_le_left (a := W i) (b := W j)) hle (b i) (hres i inf_le_left) (hb i)
    have h2 := tensorPairing_res_eq_unitSection_of_map_eq ψ
      (inf_le_right (a := W i) (b := W j)) hle (b j) (hres j inf_le_right) (hb j)
    show N.val.map (Opens.infLELeft (W i) (W j)).op (b i)
      = N.val.map (Opens.infLERight (W i) (W j)).op (b j)
    refine tensorPairing_left_injective_of_forall_germ_notMem_maximalIdeal_smul_top ψ
      (W i ⊓ W j) (L.val.restrictₛₗ (homOfLE hle).op t) hgerm ?_
    exact h1.trans h2.symm
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    ((SheafOfModules.toSheaf (structureSheafRing X)).obj N) W V
    (fun i => homOfLE (hWV i)) hcover b hcompat
  refine ⟨g, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq'
    ((SheafOfModules.toSheaf (structureSheafRing X)).obj
      (SheafOfModules.unit (structureSheafRing X))) W V
    (fun i => homOfLE (hWV i)) hcover _ _ ?_
  intro i
  have hgi : N.val.map (homOfLE (hWV i)).op g = b i := hg i
  have h1 : (SheafOfModules.unit (structureSheafRing X)).val.map (homOfLE (hWV i)).op
        (tensorPairing ψ V t g) = unitSection X (W i) :=
    (tensorPairing_res ψ (homOfLE (hWV i)) t g).trans (by rw [hgi]; exact hb i)
  have h2 : (SheafOfModules.unit (structureSheafRing X)).val.map (homOfLE (hWV i)).op
        (unitSection X V) = unitSection X (W i) :=
    map_one ((structureSheafRing X).obj.map (homOfLE (hWV i)).op).hom
  exact h1.trans h2.symm

end Glue

end Stacks.SheafOfModules

end

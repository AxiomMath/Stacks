module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.MeromorphicSections
public import StacksFrontier.AlgebraicGeometry.Divisors.MeromorphicStalk.BaseChange
public import StacksFrontier.AlgebraicGeometry.Divisors.MeromorphicStalk.Sheafify
public import StacksFrontier.Topology.Sheaves.Presheaf.LocalizationStalk
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of the sheaf of meromorphic sections

Let `𝒪` be a sheaf of commutative rings on a topological space `X`, let `𝒦` be its sheaf of
total quotient rings and let `F` be a sheaf of `𝒪`-modules. The sheaf of meromorphic sections
of `F` is `𝒦(F) = 𝒦 ⊗_𝒪 F`, the sheafification of the sectionwise tensor product. Immediately
after its definition the source records the computation of its stalks:
`𝒦(F)_x = 𝒦_x ⊗_{𝒪_x} F_x = S_x^{-1} F_x`, where `S` is the subsheaf of regular sections of
`𝒪` and `S_x` its stalk — the germs at `x` represented by a section which is a nonzerodivisor
at every point of some neighbourhood.

This file proves both equalities. The first is the specialization to `𝒪 ⟶ 𝒦` of the general
statement that a sectionwise extension of scalars is computed stalkwise
(`Stacks.ModuleStalk.isBaseChange_toChangeOfRingsStalk`) composed with the fact that
sheafification does not change stalks
(`Stacks.ModuleStalk.sheafifyModulesStalkEquiv`). The second follows because `𝒦_x` is the
localization of `𝒪_x` at `S_x` (Stacks 01D0, in the form
`Stacks.Presheaf.Localization.isLocalization_stalk_localizationSheaf`), so a base change along
`𝒪_x → 𝒦_x` is the same thing as a localization of modules at `S_x`.

The form in which this is meant to be used downstream is
`Stacks.Divisors.exists_nhds_smul_eq`: a section `s` of `𝒦(F)` over an open set `U` has, on
some neighbourhood `V` of any prescribed point of `U`, a *denominator* — a section `b` of `𝒪`
which is a nonzerodivisor in the local ring at every point of `V`, with `b · s|_V` the image of a
section of `F`. That is the local normal form `s = a / b` with `b` a nonzerodivisor, which is
what the quasi-coherence and nowhere-dense-support parts of Tag 02P0 rest on. Its stalkwise
shadow is `Stacks.Divisors.exists_regularGerm_smul_eq`.

## Main definitions

* `Stacks.Divisors.toMeromorphicSectionSheaf`: the canonical morphism `F ⟶ 𝒦(F)` of presheaves
  of `𝒪`-modules, and `Stacks.Divisors.toMeromorphicSectionStalk` the linear map it induces on
  the stalk at a point.
* `Stacks.Divisors.meromorphicSectionStalkEquiv`: the resulting linear equivalence
  `𝒦_x ⊗_{𝒪_x} F_x ≃ 𝒦(F)_x`.
* `Stacks.Divisors.regularGerms`: the multiplicative set `S_x` of germs of regular sections.

## Main results

* `Stacks.Divisors.isBaseChange_toMeromorphicSectionStalk`: `𝒦(F)_x = 𝒦_x ⊗_{𝒪_x} F_x`.
* `Stacks.Divisors.isLocalizedModule_toMeromorphicSectionStalk`: `𝒦(F)_x = S_x^{-1} F_x`.
* `Stacks.Divisors.exists_regularGerm_smul_eq`: every germ of a meromorphic section has a
  denominator.
* `Stacks.Divisors.exists_nhds_smul_eq`: the same on a neighbourhood — a section of `𝒦(F)` over
  an open set is, near each of its points, a section of `F` divided by a nonzerodivisor.
* `Stacks.Divisors.germ_mem_regularGerms` and
  `Stacks.Divisors.regularGerms_le_nonZeroDivisors`: how to produce a regular germ, and the fact
  that one is a nonzerodivisor in the local ring.

## Implementation notes

No declaration here carries the tag `01X4`. The two definitions of that tag are already
formalized, as `AlgebraicGeometry.meromorphicSectionSheaf` and
`AlgebraicGeometry.MeromorphicSection`, and they carry it; the remaining content of the tag's
page is the display proved here *together with* the assertion that `𝒦_x` injects into the total
quotient ring of `𝒪_x` with equality exactly when `S_x` is the set of all nonzerodivisors,
which is not proved here. So the covering set of the tag is incomplete.

The sheaf `𝒦(F)` is `AlgebraicGeometry.meromorphicSectionSheaf`, which is by definition (and by
`rfl`) the sheafification of the sectionwise tensor product, so the general results of
`StacksFrontier.AlgebraicGeometry.Divisors.MeromorphicStalk.BaseChange` and
`.Sheafify` apply to it directly. Likewise the morphism `F ⟶ 𝒦(F)` defined here agrees by
`rfl`, on sections, with the explicit unit of extension of scalars used by the formalization of
Tag 02P0: both send a section `l` to the image of `1 ⊗ l` under the sheafification map.

The `Module ↑(𝒪.presheaf.stalk x)` structures on the stalks are declared as instances in this
file because instance search cannot see them: the sheaves of modules involved are indexed by
`Stacks.ModuleStalk.ringSheafOn`, which search does not reduce to the composite with
`forget₂ CommRingCat RingCat` that Mathlib's stalk instance is stated for. For the same reason a
consumer working on a scheme `X` must spell the local ring `X.sheaf.presheaf.stalk x` rather than
`X.presheaf.stalk x`; the two are equal by `rfl`, but only the first is matched by instance
search against the statements here.

## References

* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 01D0](https://stacks.math.columbia.edu/tag/01D0)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace TensorProduct
open AlgebraicGeometry Stacks.ModuleStalk

universe u

namespace Stacks.Divisors

variable {X : TopCat.{u}} (O : TopCat.Sheaf CommRingCat.{u} X)
  (F : SheafOfModules.{u} (ringSheafOn O))

/-- The canonical morphism `𝒪 ⟶ 𝒦` of presheaves of commutative rings to the sheaf of total
quotient rings. -/
abbrev toTotalQuotient : O.presheaf ⟶ (totalQuotientSheaf O).presheaf :=
  (toTotalQuotientSheaf O).hom

/-- The sectionwise tensor product `𝒦 ⊗_𝒪 F`, before sheafification: its sections over an open
set `U` are `𝒦(U) ⊗_{𝒪(U)} F(U)`. -/
abbrev meromorphicSectionPresheaf : PresheafOfModules.{u}
    ((totalQuotientSheaf O).presheaf ⋙ forget₂ CommRingCat RingCat) :=
  changeOfRings (toTotalQuotient O) F.val

/-- The canonical morphism `F ⟶ 𝒦(F)` of presheaves of `𝒪`-modules: the unit of extension of
scalars followed by the sheafification map. On sections it sends `l` to the image of `1 ⊗ l`. -/
def toMeromorphicSectionSheaf :
    F.val ⟶ (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (toTotalQuotient O)).obj
      (meromorphicSectionSheaf O F).val :=
  toChangeOfRings (toTotalQuotient O) F.val ≫
    (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (toTotalQuotient O)).map
      (toSheafifyModules (totalQuotientSheaf O) (meromorphicSectionPresheaf O F))

/-- `𝒦(F)` read as a presheaf of `𝒪`-modules, by restriction of scalars along `𝒪 ⟶ 𝒦`. This is
the form in which the source regards `F` as a subsheaf of `𝒦(F)`. -/
abbrev meromorphicSectionRestrict : PresheafOfModules.{u}
    (O.presheaf ⋙ forget₂ CommRingCat RingCat) :=
  (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (toTotalQuotient O)).obj
    (meromorphicSectionSheaf O F).val

/-- The stalk of `𝒦(F)` is a module over the stalk of `𝒪`, by restriction of scalars along
`𝒪 ⟶ 𝒦`. -/
instance moduleStalkMeromorphicSectionSheaf (x : X) :
    Module ↑(O.presheaf.stalk x) ↑((presheafOn (meromorphicSectionSheaf O F).val).stalk x) :=
  moduleStalk (O := O.presheaf)
    ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (toTotalQuotient O)).obj
      (meromorphicSectionSheaf O F).val) x

/-- The map `F_x → 𝒦(F)_x` induced on stalks by the canonical morphism `F ⟶ 𝒦(F)`, as a linear
map over the local ring `𝒪_x`. -/
def toMeromorphicSectionStalk (x : X) :
    ↑((presheafOn F.val).stalk x) →ₗ[O.presheaf.stalk x]
      ↑((presheafOn (meromorphicSectionSheaf O F).val).stalk x) :=
  stalkMap (toMeromorphicSectionSheaf O F) x

/-- The map `F_x → 𝒦(F)_x` sends the germ of a section `m` to the germ of the image of
`1 ⊗ m`. -/
theorem toMeromorphicSectionStalk_germ (x : X) (W : Opens X) (hx : x ∈ W)
    (m : ↑(F.val.obj (op W))) :
    toMeromorphicSectionStalk O F x (germ F.val W x hx m) =
      germ (meromorphicSectionSheaf O F).val W x hx
        (((toSheafifyModules (totalQuotientSheaf O) (meromorphicSectionPresheaf O F)).app
          (op W)).hom (cofTmul (toTotalQuotient O) F.val W 1 m)) :=
  (stalkMap_germ (toMeromorphicSectionSheaf O F) x W hx m).trans
    (congrArg (fun y => germ (meromorphicSectionSheaf O F).val W x hx
      (((toSheafifyModules (totalQuotientSheaf O) (meromorphicSectionPresheaf O F)).app
        (op W)).hom y)) (toChangeOfRings_app (toTotalQuotient O) F.val W m))

/-- The map `F_x → 𝒦(F)_x` is the comparison map to the stalk of the sectionwise tensor product
followed by the stalk map of sheafification. -/
theorem toMeromorphicSectionStalk_eq (x : X) :
    toMeromorphicSectionStalk O F x =
      (stalkMap ((Stacks.PresheafOfModules.ChangeOfRings.restrictScalars (toTotalQuotient O)).map
          (toSheafifyModules (totalQuotientSheaf O) (meromorphicSectionPresheaf O F))) x).comp
        (toChangeOfRingsStalk (toTotalQuotient O) F.val x) :=
  stalkMap_comp _ _ x

/-- The two scalar actions on the stalk of `𝒦(F)` — that of `𝒪_x` by restriction of scalars and
that of `𝒦_x` through the structure map — are compatible. -/
theorem isScalarTower_stalk_meromorphicSectionSheaf (x : X)
    [Algebra ↑(O.presheaf.stalk x) ↑((totalQuotientSheaf O).presheaf.stalk x)]
    (halg : algebraMap ↑(O.presheaf.stalk x) ↑((totalQuotientSheaf O).presheaf.stalk x) =
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map (toTotalQuotient O)).hom) :
    IsScalarTower ↑(O.presheaf.stalk x) ↑((totalQuotientSheaf O).presheaf.stalk x)
      ↑((presheafOn (meromorphicSectionSheaf O F).val).stalk x) :=
  isScalarTower_of_germ_smul (toTotalQuotient O) x halg fun _ hx r t =>
    (presheafGerm_smul (meromorphicSectionRestrict O F) hx r t).symm

/-- **The stalk of the sheaf of meromorphic sections.** At every point `x` the canonical map
`F_x → 𝒦(F)_x` exhibits the stalk of the sheaf of meromorphic sections of `F` as the base change
of `F_x` along `𝒪_x → 𝒦_x`; that is, `𝒦(F)_x = 𝒦_x ⊗_{𝒪_x} F_x`. -/
theorem isBaseChange_toMeromorphicSectionStalk (x : X) :
    letI := stalkAlgebra (toTotalQuotient O) x
    letI := isScalarTower_stalk_meromorphicSectionSheaf O F x rfl
    IsBaseChange ↑((totalQuotientSheaf O).presheaf.stalk x)
      (toMeromorphicSectionStalk O F x) := by
  let := stalkAlgebra (toTotalQuotient O) x
  let := isScalarTower_stalk_meromorphicSectionSheaf O F x rfl
  refine IsBaseChange.of_equiv
    ((changeOfRingsStalkEquiv (toTotalQuotient O) F.val x rfl).trans
      (sheafifyModulesStalkEquiv (totalQuotientSheaf O) (meromorphicSectionPresheaf O F) x))
    fun m => ?_
  exact (congrArg
      (sheafifyModulesStalkEquiv (totalQuotientSheaf O) (meromorphicSectionPresheaf O F) x)
      (one_smul ↑((totalQuotientSheaf O).presheaf.stalk x)
        (toChangeOfRingsStalk (toTotalQuotient O) F.val x m))).trans
    (LinearMap.congr_fun (toMeromorphicSectionStalk_eq O F x) m).symm

/-- The stalk of the sheaf of meromorphic sections, as a linear equivalence
`𝒦_x ⊗_{𝒪_x} F_x ≃ 𝒦(F)_x`. -/
def meromorphicSectionStalkEquiv (x : X) :
    letI := stalkAlgebra (toTotalQuotient O) x
    TensorProduct ↑(O.presheaf.stalk x) ↑((totalQuotientSheaf O).presheaf.stalk x)
        ↑((presheafOn F.val).stalk x) ≃ₗ[(totalQuotientSheaf O).presheaf.stalk x]
      ↑((presheafOn (meromorphicSectionSheaf O F).val).stalk x) :=
  let := stalkAlgebra (toTotalQuotient O) x
  let := isScalarTower_stalk_meromorphicSectionSheaf O F x rfl
  (isBaseChange_toMeromorphicSectionStalk O F x).equiv

/-- The multiplicative set `S_x` of germs at `x` of regular sections of `𝒪`: the germs
represented, on some neighbourhood of `x`, by a section which is a nonzerodivisor in the local
ring at every point of that neighbourhood. -/
abbrev regularGerms (x : X) : Submonoid ↑(O.presheaf.stalk x) :=
  (O.presheaf.submonoidPresheafOfStalk
    fun y => nonZeroDivisors ↑(O.presheaf.stalk y)).stalk x

/-- The germ at `x` of a section of `𝒪` which is a nonzerodivisor in the local ring at every
point of its domain is a regular germ. -/
theorem germ_mem_regularGerms (x : X) (W : Opens X) (hx : x ∈ W)
    (b : ↑(O.presheaf.obj (op W)))
    (hb : ∀ (y : X) (hy : y ∈ W),
      O.presheaf.germ W y hy b ∈ nonZeroDivisors ↑(O.presheaf.stalk y)) :
    O.presheaf.germ W x hx b ∈ regularGerms O x :=
  Submonoid.mem_iSup_of_mem W (Submonoid.mem_iSup_of_mem hx
    (Submonoid.mem_map_of_mem _ (Submonoid.mem_iInf.mpr fun y => hb y y.2)))

/-- A regular germ is a nonzerodivisor in the local ring. The converse can fail: the source
warns that `S_x` need not be all of the nonzerodivisors of `𝒪_x`. -/
theorem regularGerms_le_nonZeroDivisors (x : X) :
    regularGerms O x ≤ nonZeroDivisors ↑(O.presheaf.stalk x) := by
  refine iSup_le fun W => iSup_le fun hx => ?_
  rw [Submonoid.map_le_iff_le_comap]
  intro b hb
  exact Submonoid.mem_iInf.mp hb ⟨x, hx⟩

/-- A regular germ is the germ of a section which is a nonzerodivisor at every point of some
neighbourhood. The point is that the submonoids whose supremum defines `S_x` form a directed
family, the neighbourhoods of `x` being closed under intersection. -/
theorem exists_germ_eq_of_mem_regularGerms (x : X) {c : ↑(O.presheaf.stalk x)}
    (hc : c ∈ regularGerms O x) :
    ∃ (W : Opens X) (hx : x ∈ W) (b : ↑(O.presheaf.obj (op W))),
      (∀ (y : X) (hy : y ∈ W),
        O.presheaf.germ W y hy b ∈ nonZeroDivisors ↑(O.presheaf.stalk y)) ∧
      O.presheaf.germ W x hx b = c := by
  set S := O.presheaf.submonoidPresheafOfStalk
    fun y => nonZeroDivisors ↑(O.presheaf.stalk y) with hSdef
  have key : ∀ (W W' : Opens X) (h : W' ≤ W) (hxW' : x ∈ W'),
      (S.obj (op W)).map (O.presheaf.germ W x (h hxW')).hom ≤
        (S.obj (op W')).map (O.presheaf.germ W' x hxW').hom := by
    intro W W' h hxW'
    rw [Submonoid.map_le_iff_le_comap]
    intro b hb
    exact ⟨(O.presheaf.map (homOfLE h).op).hom b, S.map (homOfLE h).op hb,
      O.presheaf.germ_res_apply (homOfLE h) x hxW' b⟩
  have hdir : Directed (· ≤ ·) (fun V : {U : Opens X // x ∈ U} =>
      (S.obj (op V.1)).map (O.presheaf.germ V.1 x V.2).hom) := fun V₁ V₂ =>
    ⟨⟨V₁.1 ⊓ V₂.1, V₁.2, V₂.2⟩, key V₁.1 _ inf_le_left _, key V₂.1 _ inf_le_right _⟩
  have hne : Nonempty {U : Opens X // x ∈ U} := ⟨⟨⊤, trivial⟩⟩
  have hle : (⨆ (U : Opens X) (hxU : x ∈ U),
      (S.obj (op U)).map (O.presheaf.germ U x hxU).hom) ≤
      ⨆ V : {U : Opens X // x ∈ U}, (S.obj (op V.1)).map (O.presheaf.germ V.1 x V.2).hom :=
    iSup_le fun U => iSup_le fun hxU =>
      le_iSup (fun V : {U : Opens X // x ∈ U} =>
        (S.obj (op V.1)).map (O.presheaf.germ V.1 x V.2).hom) ⟨U, hxU⟩
  obtain ⟨V, hV⟩ := (Submonoid.mem_iSup_of_directed hdir).mp (hle hc)
  obtain ⟨b, hb, hbc⟩ := Submonoid.mem_map.mp hV
  exact ⟨V.1, V.2, b, fun y hy => Submonoid.mem_iInf.mp hb ⟨y, hy⟩, hbc⟩

/-- **The stalk of the sheaf of meromorphic sections is a localization.** At every point `x` the
canonical map `F_x → 𝒦(F)_x` exhibits the stalk of the sheaf of meromorphic sections of `F` as
the localization of `F_x` at the germs of regular sections; that is,
`𝒦(F)_x = S_x^{-1} F_x`. -/
@[ega "IV 20.1.3" "partial"]
theorem isLocalizedModule_toMeromorphicSectionStalk (x : X) :
    IsLocalizedModule (regularGerms O x) (toMeromorphicSectionStalk O F x) := by
  let := stalkAlgebra (toTotalQuotient O) x
  let := isScalarTower_stalk_meromorphicSectionSheaf O F x rfl
  have hloc : IsLocalization (regularGerms O x)
      ↑((totalQuotientSheaf O).presheaf.stalk x) :=
    Stacks.Presheaf.Localization.isLocalization_stalk_localizationSheaf
      ⟨X, O.presheaf, O.presheaf.submonoidPresheafOfStalk
        fun y => nonZeroDivisors ↑(O.presheaf.stalk y)⟩ x
  exact (isLocalizedModule_iff_isBaseChange (regularGerms O x)
    ↑((totalQuotientSheaf O).presheaf.stalk x) (toMeromorphicSectionStalk O F x)).mpr
      (isBaseChange_toMeromorphicSectionStalk O F x)

/-- **Local normal form of a meromorphic section.** Every germ of a meromorphic section of `F`
at `x` has a denominator: a germ `b` of a regular section of `𝒪` and a germ `a` of a section of
`F` with `b • z` the image of `a`. This is the statement `z = a / b` with `b` a nonzerodivisor,
read in the stalk. -/
theorem exists_regularGerm_smul_eq (x : X)
    (z : ↑((presheafOn (meromorphicSectionSheaf O F).val).stalk x)) :
    ∃ b ∈ regularGerms O x, ∃ a : ↑((presheafOn F.val).stalk x),
      b • z = toMeromorphicSectionStalk O F x a := by
  have := isLocalizedModule_toMeromorphicSectionStalk O F
  obtain ⟨⟨a, b⟩, hb⟩ := IsLocalizedModule.surj (regularGerms O x)
    (toMeromorphicSectionStalk O F x) z
  exact ⟨b.1, b.2, a, hb⟩

/-- **The local normal form of a meromorphic section.** Let `s` be a section of `𝒦(F)` over an
open set `U` and let `x ∈ U`. Then on some open neighbourhood `V ≤ U` of `x` there are a section
`b` of `𝒪`, a nonzerodivisor in the local ring at every point of `V`, and a section `a` of `F`,
with `b · s|_V` the image of `a`. This is the statement `s = a / b` with `b` a nonzerodivisor,
holding locally. -/
theorem exists_nhds_smul_eq (x : X) (U : Opens X) (hx : x ∈ U)
    (s : ↑((meromorphicSectionRestrict O F).obj (op U))) :
    ∃ (V : Opens X) (hVU : V ≤ U) (_ : x ∈ V) (b : ↑(O.presheaf.obj (op V))),
      (∀ (y : X) (hy : y ∈ V),
        O.presheaf.germ V y hy b ∈ nonZeroDivisors ↑(O.presheaf.stalk y)) ∧
      ∃ a : ↑(F.val.obj (op V)),
        b • res (meromorphicSectionRestrict O F) hVU s =
          ((toMeromorphicSectionSheaf O F).app (op V)).hom a := by
  obtain ⟨c, hc, a₀, ha₀⟩ := exists_regularGerm_smul_eq O F x
    (germ (meromorphicSectionRestrict O F) U x hx s)
  obtain ⟨W, hxW, b, hbreg, hbc⟩ := exists_germ_eq_of_mem_regularGerms O x hc
  obtain ⟨W', hW'le, hxW', a, ha⟩ :=
    exists_le_germ_eq F.val a₀ (show x ∈ U ⊓ W from ⟨hx, hxW⟩)
  have hW'U : W' ≤ U := hW'le.trans inf_le_left
  have hW'W : W' ≤ W := hW'le.trans inf_le_right
  obtain ⟨b, hbreg, hbc⟩ : ∃ b : ↑(O.presheaf.obj (op W')),
      (∀ (y : X) (hy : y ∈ W'),
        O.presheaf.germ W' y hy b ∈ nonZeroDivisors ↑(O.presheaf.stalk y)) ∧
      O.presheaf.germ W' x hxW' b = c :=
    ⟨(O.presheaf.map (homOfLE hW'W).op).hom b, fun y hy => by
      rw [O.presheaf.germ_res_apply (homOfLE hW'W) y hy b]; exact hbreg y _,
      by rw [O.presheaf.germ_res_apply (homOfLE hW'W) x hxW' b]; exact hbc⟩
  have hkey : germ (meromorphicSectionRestrict O F) W' x hxW'
        (b • res (meromorphicSectionRestrict O F) hW'U s) =
      germ (meromorphicSectionRestrict O F) W' x hxW'
        (((toMeromorphicSectionSheaf O F).app (op W')).hom a) := by
    rw [presheafGerm_smul (meromorphicSectionRestrict O F) hxW', hbc,
      germ_res (meromorphicSectionRestrict O F) hW'U hxW' s]
    exact ha₀.trans ((congrArg (stalkMap (toMeromorphicSectionSheaf O F) x) ha).symm.trans
      (stalkMap_germ (toMeromorphicSectionSheaf O F) x W' hxW' a))
  obtain ⟨V, hxV, iW, iW', hV⟩ := TopCat.Presheaf.germ_eq
    (presheafOn (meromorphicSectionRestrict O F)) x hxW' hxW' _ _ hkey
  cases Subsingleton.elim iW iW'
  refine ⟨V, (leOfHom iW).trans hW'U, hxV, (O.presheaf.map (homOfLE (leOfHom iW)).op).hom b,
    fun y hy => ?_, res F.val (leOfHom iW) a, ?_⟩
  · rw [O.presheaf.germ_res_apply (homOfLE (leOfHom iW)) y hy b]
    exact hbreg y _
  · exact (congrArg (_ • ·) (res_res _ hW'U (leOfHom iW) s).symm).trans
      ((res_smul _ (leOfHom iW) b _).symm.trans
        (hV.trans (res_app (toMeromorphicSectionSheaf O F) (leOfHom iW) a)))

end Stacks.Divisors

end


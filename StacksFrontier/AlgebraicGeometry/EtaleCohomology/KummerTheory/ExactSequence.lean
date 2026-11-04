module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.KummerTheory.FirstCohomologyOfRootsOfUnity

/-!
# The Kummer exact sequence in degree one

Let `S` be a scheme, `n` a natural number, and fix a site over `S` on which the Kummer sequence
`0 ⟶ μ_n ⟶ 𝐆_m ⟶ 𝐆_m ⟶ 0` of abelian sheaves is short exact and which has a terminal object.
The long exact sequence of that short exact sequence identifies the two ends of
`H¹(S, μ_n)`: its kernel in `H¹(S, 𝐆_m)` is exactly the image of the Kummer boundary, and its
image in `H¹(S, 𝐆_m)` is exactly the `n`-torsion, because the second map of the Kummer sequence
is multiplication by `n`.

## Main results

* `AlgebraicGeometry.exists_terminalBoundary_iff`: for a short exact sequence of abelian sheaves
  on a site with a terminal object, a class in the first cohomology of the kernel sheaf is the
  boundary of a global section of the quotient sheaf exactly when it dies in the first cohomology
  of the middle sheaf.
* `AlgebraicGeometry.exists_kummerBoundary_iff`: **Tag 040Q, the image of the pairs with trivial
  invertible sheaf.** A class in `H¹(S, μ_n)` is the class of such a pair exactly when its image
  in `H¹(S, 𝐆_m)` vanishes.
* `AlgebraicGeometry.exists_kummerFirstCohomologyMap_iff`: **Tag 040Q, the image of `H¹(S, μ_n)`
  in `H¹(S, 𝐆_m)`.** It is exactly the `n`-torsion.

## Implementation notes

Both results come from Mathlib's long exact sequence for `Ext` in the second variable,
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₁` and
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₂`, applied to the Kummer sequence with the
constant sheaf of integers in the first variable, which is what `CategoryTheory.Sheaf.H` is the
`Ext` out of. Turning the resulting class in `Ext⁰` of the quotient sheaf into a global unit uses
that over a terminal object a morphism from the constant presheaf of integers is determined by,
and determines, a single section: that is `AlgebraicGeometry.terminalSectionMorphism_app_one`.
That the `n`-th power map induces multiplication by `n` on cohomology is
`AlgebraicGeometry.firstCohomologyMap_nsmul_id`, since the `n`-th power map is `n • 𝟙` on the
sheaf of units written additively.

What this file does **not** prove, and what Tag 040Q asserts beyond it: that every class in
`H¹(S, μ_n)` is the class of a pair. By the two results above that is equivalent to every
`n`-torsion class of `H¹(S, 𝐆_m)` being the class of an invertible sheaf `ℒ` on `S`, which is
the identification `H¹(S, 𝐆_m) = Pic(S)` of Tag 03P8 for the topology in question. The library
has that identification only for the Zariski topology
(`Stacks.Picard.ZariskiSite.zariskiH1UnitsAddEquivPicardGroup`). Each remaining comparison
factors as `H¹_τ(S, 𝐆_m) = Pic(𝒪_τ)`, which is Tag 040E on the `τ` site, then
`Pic(𝒪_τ) = Pic(S)`, which is Tag 03DX. At `τ = étale` on the small site Tag 03DX *is*
available, unconditionally, as `AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`;
what is missing there is Tag 040E, stated for `RingedSite.{u, u, u}` while the small étale
ringed site is `RingedSite.{u + 1, u, u}`, together with a transport of the Picard group along
the Tag 03DX equivalence. On the big fppf and syntomic sites it is clause (1) of Tag 03DX that
is undischarged (`BigFppfOver.QuasicoherentIsEssImageAssociatedModule`). No part of Tag 040Q
is assumed here: the statements below are unconditional consequences of short exactness.

## References

* [Stacks Project, Tag 040Q](https://stacks.math.columbia.edu/tag/040Q)
* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 03P8](https://stacks.math.columbia.edu/tag/03P8)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

universe w t v u u₁ v₁

/-- The boundary of a morphism to the quotient of a short exact sequence dies in the middle
object: the extension class is annihilated by the inclusion of the kernel. -/
private theorem ext_boundary_comp_mk₀_f {D : Type u₁} [Category.{v₁} D] [Abelian D]
    [HasExt.{w} D] {S : ShortComplex D} (hS : S.ShortExact) {X : D} (q : X ⟶ S.X₃) :
    ((Abelian.Ext.mk₀ q).comp hS.extClass (zero_add 1)).comp
        (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 := by
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero, hS.extClass_comp, Abelian.Ext.comp_zero]

section Boundary

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- A morphism from the constant presheaf of integers is the one determined by its value at `1`
over a terminal object of the site. -/
theorem terminalSectionMorphism_app_one (A : Cᵒᵖ ⥤ AddCommGrpCat.{t}) {T : C} (hT : IsTerminal T)
    (r : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ A) :
    terminalSectionMorphism A hT (r.app (op T) ⟨1⟩) = r := by
  refine constInt_hom_ext _ _ fun U => ?_
  rw [terminalSectionMorphism_one, terminalFamily]
  exact (NatTrans.naturality_apply r (hT.from U.unop).op (⟨1⟩ : ULift.{t} ℤ)).symm

variable [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w} (Sheaf J AddCommGrpCat.{t})]

/-- **The boundary classes are exactly those that die in the middle sheaf.** For a short exact
sequence of abelian sheaves on a site with a terminal object, a first cohomology class of the
kernel sheaf is the boundary of a global section of the quotient sheaf exactly when its image in
the first cohomology of the middle sheaf vanishes. -/
theorem exists_terminalBoundary_iff (S : ShortComplex (Sheaf J AddCommGrpCat.{t}))
    (hS : S.ShortExact) {T : C} (hT : IsTerminal T) (x : Sheaf.H S.X₁ 1) :
    (∃ y : S.X₃.obj.obj (op T), terminalBoundary S hS hT y = x) ↔
      Sheaf.H.map S.f 1 x = 0 := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ext_boundary_comp_mk₀_f hS _
  · intro hx
    obtain ⟨z, hz⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x hx (zero_add 1)
    obtain ⟨q, rfl⟩ := (Abelian.Ext.mk₀_bijective _ S.X₃).2 z
    refine ⟨(((sheafificationAdjunction J AddCommGrpCat).homEquiv _ S.X₃) q).app (op T) ⟨1⟩, ?_⟩
    rw [terminalBoundary_eq, terminalSectionMorphism_app_one]
    exact (congrArg (fun w => (Abelian.Ext.mk₀ w).comp hS.extClass (zero_add 1))
      (Equiv.symm_apply_apply _ q)).trans hz

end Boundary

section Kummer

variable {C : Type v} [Category.{u} C]

/-- Every section of the sheaf of units over an object of the site is a global unit of the scheme
attached to it. -/
theorem unitsSection_surjective (F : C ⥤ Scheme.{u}) (T : C) :
    Function.Surjective (unitsSection F T) :=
  fun y => ⟨Additive.toMul y, rfl⟩

variable (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
  (hF : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ)
  [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})]

/-- The zero morphism induces zero on cohomology. -/
theorem firstCohomologyMap_zero {G G' : Sheaf J AddCommGrpCat.{u}} (q : ℕ) (y : Sheaf.H G q) :
    Sheaf.H.map (0 : G ⟶ G') q y = 0 := by
  simpa using Sheaf.H.map_add_apply (0 : G ⟶ G') 0 y

/-- A natural multiple of the identity induces that multiple of the identity on cohomology. -/
theorem firstCohomologyMap_nsmul_id {G : Sheaf J AddCommGrpCat.{u}} (m q : ℕ)
    (y : Sheaf.H G q) : Sheaf.H.map (m • 𝟙 G) q y = m • y := by
  induction m with
  | zero => simpa using firstCohomologyMap_zero J q y
  | succ m ih => rw [succ_nsmul, Sheaf.H.map_add_apply, ih, Sheaf.H.map_id_apply, succ_nsmul]

omit [HasSheafify J AddCommGrpCat.{u}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u})] in
/-- The second map of the Kummer sequence is `n` times the identity of the sheaf of units. -/
theorem kummerSequence_g_eq_nsmul_id :
    (kummerSequence J F hF n).g = n • 𝟙 (unitsSheaf J F hF) :=
  rfl

/-- **The `n`-th power map of the Kummer sequence is multiplication by `n` on cohomology.** -/
theorem kummerSequence_firstCohomologyMap_g (y : Sheaf.H (kummerSequence J F hF n).X₂ 1) :
    Sheaf.H.map (kummerSequence J F hF n).g 1 y = n • y := by
  rw [kummerSequence_g_eq_nsmul_id]
  exact firstCohomologyMap_nsmul_id J n 1 y

variable (hS : (kummerSequence J F hF n).ShortExact) {T : C} (hT : IsTerminal T)

/-- **Stacks Project, Tag 040Q, the image of the pairs whose invertible sheaf is trivial.** A
class in `H¹(S, μ_n)` is the class of such a pair — equivalently, a Kummer boundary — exactly
when its image in `H¹(S, 𝐆_m)` vanishes. So the injection of
`AlgebraicGeometry.pairIso_iff_kummerBoundary_eq` has for its image precisely the kernel of
`H¹(S, μ_n) ⟶ H¹(S, 𝐆_m)`. -/
@[stacks 040Q "the image of the pairs with trivial invertible sheaf in H^1 of the roots of \
unity is exactly the kernel of the map to H^1 of the multiplicative group; so the injection of \
pairIso_iff_kummerBoundary_eq misses exactly the classes with nonzero image there"]
theorem exists_kummerBoundary_iff (x : Sheaf.H (kummerSequence J F hF n).X₁ 1) :
    (∃ a : (Scheme.Γ.obj (op (F.obj T)))ˣ, kummerBoundary J F hF n hS hT a = x) ↔
      Sheaf.H.map (kummerSequence J F hF n).f 1 x = 0 := by
  refine Iff.trans ?_ (exists_terminalBoundary_iff (kummerSequence J F hF n) hS hT x)
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨unitsSection F T a, ha⟩
  · rintro ⟨y, hy⟩
    obtain ⟨a, rfl⟩ := unitsSection_surjective F T y
    exact ⟨a, hy⟩

include hS in
/-- **Stacks Project, Tag 040Q, the image of `H¹(S, μ_n)` in `H¹(S, 𝐆_m)`.** It is exactly the
`n`-torsion subgroup, since the second map of the Kummer sequence induces multiplication by `n`
on first cohomology. -/
@[stacks 040Q "the image of H^1 of the roots of unity in H^1 of the multiplicative group is \
exactly the n-torsion; with the kernel computed by exists_kummerBoundary_iff this presents \
H^1(S, mu_n) as an extension of that n-torsion by the global units modulo nth powers. What \
remains between this and the full statement of 040Q is the abelian-group structure on \
AlgebraicGeometry.PairClasses, for which no AddCommGroup instance exists, together with the \
comparison homomorphism to H^1; Tag 03P8 is NOT the gap, being proved at \
Picard/MultiplicativeGroupFirstCohomology.lean:206"]
theorem exists_kummerFirstCohomologyMap_iff (y : Sheaf.H (kummerSequence J F hF n).X₂ 1) :
    (∃ x : Sheaf.H (kummerSequence J F hF n).X₁ 1,
        Sheaf.H.map (kummerSequence J F hF n).f 1 x = y) ↔ n • y = 0 := by
  refine ⟨?_, fun hy => Abelian.Ext.covariant_sequence_exact₂ _ hS y ?_⟩
  · rintro ⟨x, rfl⟩
    rw [← kummerSequence_firstCohomologyMap_g, ← Sheaf.H.map_comp_apply,
      (kummerSequence J F hF n).zero]
    exact firstCohomologyMap_zero J 1 x
  · rwa [← Sheaf.H.map_apply, kummerSequence_firstCohomologyMap_g]

/-- **Stacks Project, Tag 040Q, the obstruction to surjectivity.** The pairs whose invertible
sheaf is trivial exhaust `H¹(S, μ_n)` exactly when `H¹(S, 𝐆_m)` has no `n`-torsion. So the
classes of Tag 040Q that the trivial-invertible-sheaf part misses are measured by that torsion
group, and by Tag 03P8 it is the `n`-torsion of the Picard group. -/
@[stacks 040Q "the obstruction to surjectivity: the pairs with trivial invertible sheaf exhaust \
H^1 of the roots of unity exactly when H^1 of the multiplicative group has no n-torsion, so the \
missing classes are measured by that torsion group"]
theorem forall_exists_kummerBoundary_iff :
    (∀ x : Sheaf.H (kummerSequence J F hF n).X₁ 1,
        ∃ a : (Scheme.Γ.obj (op (F.obj T)))ˣ, kummerBoundary J F hF n hS hT a = x) ↔
      ∀ y : Sheaf.H (kummerSequence J F hF n).X₂ 1, n • y = 0 → y = 0 := by
  refine ⟨fun hsurj y hy => ?_, fun htor x => (exists_kummerBoundary_iff J F hF n hS hT x).2
    (htor _ ((exists_kummerFirstCohomologyMap_iff J F hF n hS _).1 ⟨x, rfl⟩))⟩
  obtain ⟨x, rfl⟩ := (exists_kummerFirstCohomologyMap_iff J F hF n hS y).2 hy
  obtain ⟨a, rfl⟩ := hsurj x
  exact (exists_kummerBoundary_iff J F hF n hS hT _).1 ⟨a, rfl⟩

end Kummer

end AlgebraicGeometry

end

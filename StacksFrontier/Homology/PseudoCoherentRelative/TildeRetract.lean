module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.Ideal.Span
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.Affine
public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfect.FiniteFreeSummands
public import StacksFrontier.RingTheory.Module.LocallyFree.FiniteProjective
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct summands of finite free modules on an affine scheme

On `Spec R` a direct summand of a finite free `𝒪_{Spec R}`-module is the sheaf `N^~` associated
to a finite projective `R`-module `N`, and therefore becomes finite free on each member of a
finite cover of `Spec R` by standard opens.

This is the affine case of Stacks 0BCI, which is the form in which Stacks 08E7 uses that lemma:
the terms of a strictly perfect complex on a standard open of `Spec A` become finite free after
refining the covering. The route here is entirely affine and avoids the general ringed-space
statement: a retract is a cokernel, cokernels of quasi-coherent modules on an affine scheme are
quasi-coherent, quasi-coherent modules on `Spec R` are exactly those of the form `N^~`, and
`M ↦ M^~` is fully faithful, so the sheaf-level retract descends to a retract of `R`-modules.
Finiteness and projectivity of `N` are then read off, and the standard-open conclusion is the
already-formalized Stacks 00NX.

## Main results

* `CategoryTheory.Retract.isColimitCokernelCofork` and `CategoryTheory.Retract.cokernelIso`
  exhibit a retract `X` of `Y` as the cokernel of `𝟙 Y - r ≫ i`.
* `CategoryTheory.Functor.FullyFaithful.retract` reflects a retract along a fully faithful
  functor.
* `Stacks.AffineTilde.isQuasicoherent_of_retract`: on an affine scheme a retract of a
  quasi-coherent module is quasi-coherent.
* `Stacks.AffineTilde.exists_finiteProjective_tilde_of_retract`: a retract of a sheaf isomorphic
  to `M^~`, with `M` a finite projective `R`-module, is `N^~` for a finite projective `R`-module
  `N`.
* `Stacks.AffineTilde.exists_finiteProjective_tilde_of_retract_free`: the same conclusion for a
  retract of a finite free sheaf `AlgebraicGeometry.SheafOfModules.free`.
* `Stacks.AffineTilde.exists_finite_span_free_away_of_retract_free`: the module `N` becomes
  finite free over `R_g` for the elements `g` of a finite family generating the unit ideal.
* `Stacks.AffineTilde.retractModules` and
  `Stacks.AffineTilde.exists_finiteProjective_tilde_of_retract_oxMod` restate the above for a
  retract in the `Stacks.StrictlyPerfect.OXMod` spelling of the category of
  `𝒪_{Spec R}`-modules.

## Implementation notes

The cokernel presentation of a retract is the one used to build a `SheafOfModules.Presentation`
for Stacks 0BCI: if `i : X ⟶ Y` and `r : Y ⟶ X` satisfy `i ≫ r = 𝟙 X`, then
`(𝟙 Y - r ≫ i) ≫ r = 0` and `r` is a cokernel of `𝟙 Y - r ≫ i`, the descent of `k : Y ⟶ T`
being `i ≫ k`. Only `Preadditive` is needed for that, so it is stated there.

The main statement takes the ambient finite free module as *some* sheaf isomorphic to `M^~`
rather than as `M^~` itself, and that is not cosmetic. The ring sheaf of `Spec R` has two
syntactic spellings, with carriers `↑(Spec R).toPresheafedSpace` and `↥(Spec R)`, and
`AlgebraicGeometry.SheafOfModules.free` elaborated against `(Spec R).Modules` picks the one that
`AlgebraicGeometry.tildeFinsupp` does not, so `rw [tildeFinsupp]` fails on a goal that visibly
contains the free sheaf. Supplying the isomorphism as an *argument* makes the identification at
term level, where defeq is checked at default transparency, and no transparency flag is needed.

The same device handles the other spelling wall. `Stacks.StrictlyPerfect.OXMod
(Spec R).toRingedSpace` is the same type as `(Spec R).Modules` but carries a different
`Category` instance, so a `CategoryTheory.Retract` over one is not syntactically one over the
other. `Stacks.AffineTilde.retractModules` rebuilds it field by field, which type-checks for the
same reason.

## References

* [Stacks Project, Tag 0BCI](https://stacks.math.columbia.edu/tag/0BCI)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u v₁ u₁

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- If `X` is a retract of `Y`, with `i : X ⟶ Y` and `r : Y ⟶ X` such that `i ≫ r = 𝟙 X`, then
`r` exhibits `X` as the cokernel of the complementary idempotent `𝟙 Y - r ≫ i`: a morphism
`k : Y ⟶ T` killed by `𝟙 Y - r ≫ i` satisfies `k = r ≫ (i ≫ k)`, and `i ≫ k` is the unique
such factorization. -/
public def Retract.isColimitCokernelCofork [Preadditive C] {X Y : C} (h : Retract X Y) :
    IsColimit (CokernelCofork.ofπ (f := 𝟙 Y - h.r ≫ h.i) h.r (by simp [h.retract])) :=
  Limits.CokernelCofork.IsColimit.ofπ _ _ (fun {_} k _ => h.i ≫ k)
    (fun {_} k hk => by
      rw [Preadditive.sub_comp, Category.id_comp, sub_eq_zero] at hk
      simpa only [Category.assoc] using hk.symm)
    (fun {_} _ _ m hm => by rw [← Category.id_comp m, ← h.retract, Category.assoc, hm])

/-- A retract `X` of `Y` is isomorphic to the cokernel of the complementary idempotent
`𝟙 Y - r ≫ i`. -/
public def Retract.cokernelIso [Preadditive C] [HasCokernels C] {X Y : C} (h : Retract X Y) :
    cokernel (𝟙 Y - h.r ≫ h.i) ≅ X :=
  IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) h.isColimitCokernelCofork

/-- A fully faithful functor reflects retracts: if `F.obj X` is a retract of `F.obj Y` then `X`
is a retract of `Y`. -/
public def Functor.FullyFaithful.retract {D : Type u₁} [Category.{v₁} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) {X Y : C} (h : Retract (F.obj X) (F.obj Y)) : Retract X Y where
  i := hF.preimage h.i
  r := hF.preimage h.r
  retract := hF.map_injective <| by
    rw [F.map_comp, hF.map_preimage, hF.map_preimage, h.retract,
      CategoryTheory.Functor.map_id]

end CategoryTheory

namespace Stacks.AffineTilde

variable {R : CommRingCat.{u}}

/-- On an affine scheme a retract of a quasi-coherent module is quasi-coherent, because it is a
cokernel of an endomorphism of that module and quasi-coherent modules on an affine scheme are
closed under cokernels. -/
public theorem isQuasicoherent_of_retract {X : Scheme.{u}} [IsAffine X] {F H : X.Modules}
    [H.IsQuasicoherent] (h : Retract F H) : F.IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso h.cokernelIso inferInstance

/-- **The affine case of Stacks 0BCI.** A direct summand of a sheaf isomorphic to `M^~`, for `M`
a finite projective `R`-module, is the sheaf `N^~` associated to a finite projective `R`-module
`N`.

The retract is quasi-coherent, hence of the form `N^~`, and `M ↦ M^~` is fully faithful, so the
sheaf-level retract descends to a retract of `N` in `M`; finiteness and projectivity of `N`
follow from the splitting. The ambient module is given up to isomorphism rather than on the nose
because the finite free sheaf a caller has in hand is spelled in whichever way its own context
produced it. -/
public theorem exists_finiteProjective_tilde_of_retract {M : ModuleCat.{u} R}
    [Module.Finite R M] [Module.Projective R M] {F H : (Spec R).Modules}
    (eH : (tilde.functor R).obj M ≅ H) (h : Retract F H) :
    ∃ N : ModuleCat.{u} R, Module.Finite R N ∧ Module.Projective R N ∧
      Nonempty ((tilde.functor R).obj N ≅ F) := by
  have : H.IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso eH inferInstance
  obtain ⟨N, ⟨e⟩⟩ : (tilde.functor R).essImage F := by
    rw [essImage_tilde]
    exact isQuasicoherent_of_retract h
  have h' : Retract N M := tilde.fullyFaithfulFunctor.retract
    ((Retract.ofIso e).trans (h.trans (Retract.ofIso eH.symm)))
  have hsplit : h'.r.hom ∘ₗ h'.i.hom = LinearMap.id := by
    rw [← ModuleCat.hom_comp, h'.retract, ModuleCat.hom_id]
  have hsurj : Function.Surjective h'.r.hom := fun n =>
    ⟨h'.i.hom n, by rw [← LinearMap.comp_apply, hsplit, LinearMap.id_apply]⟩
  exact ⟨N, Module.Finite.of_surjective h'.r.hom hsurj,
    Module.Projective.of_split h'.i.hom h'.r.hom hsplit, ⟨e⟩⟩

/-- **The affine case of Stacks 0BCI**, for the free sheaf of modules of finite rank: a direct
summand of a finite free `𝒪_{Spec R}`-module is `N^~` for a finite projective `R`-module `N`.

The finite free sheaf is `(ι →₀ R)^~` by `AlgebraicGeometry.tildeFinsupp`. -/
public theorem exists_finiteProjective_tilde_of_retract_free {ι : Type u} [Finite ι]
    {F : (Spec R).Modules} (h : Retract F (SheafOfModules.free.{u} ι)) :
    ∃ N : ModuleCat.{u} R, Module.Finite R N ∧ Module.Projective R N ∧
      Nonempty ((tilde.functor R).obj N ≅ F) :=
  exists_finiteProjective_tilde_of_retract (M := ModuleCat.of R (ι →₀ R)) (tildeFinsupp ι) h

/-- **The affine case of Stacks 0BCI, in standard opens.** A direct summand `F` of a finite free
`𝒪_{Spec R}`-module is `N^~` for an `R`-module `N` which becomes finite free over `R_g` for each
`g` in a finite family generating the unit ideal; equivalently, `F` is finite free on each member
of a finite covering of `Spec R` by standard opens.

This is `Stacks.AffineTilde.exists_finiteProjective_tilde_of_retract_free` followed by the
equivalence of "finite projective" with "finite locally free" (Stacks 00NX), whose spanning set
is shrunk to a finite one by `Ideal.span_eq_top_iff_finite`. -/
@[stacks 0BCI "affine case: a direct summand of a finite free module on Spec R",
  sga "6 I 2.15.1" "affine case"]
public theorem exists_finite_span_free_away_of_retract_free {ι : Type u} [Finite ι]
    {F : (Spec R).Modules} (h : Retract F (SheafOfModules.free.{u} ι)) :
    ∃ N : ModuleCat.{u} R, Nonempty ((tilde.functor R).obj N ≅ F) ∧
      ∃ s : Finset R, Ideal.span (s : Set R) = ⊤ ∧
        ∀ g ∈ s, Module.Free (Localization.Away g) (LocalizedModule.Away g N) ∧
          Module.Finite (Localization.Away g) (LocalizedModule.Away g N) := by
  obtain ⟨N, hfin, hproj, he⟩ := exists_finiteProjective_tilde_of_retract_free h
  have hFP : Module.Finite R N ∧ Module.Projective R N := ⟨hfin, hproj⟩
  obtain ⟨t, ht, hfree⟩ := ((Module.finite_projective_tfae R N).out 2 7).mp hFP
  obtain ⟨s, hs, hspan⟩ := (Ideal.span_eq_top_iff_finite t).mp ht
  exact ⟨N, he, s, hspan, fun g hg => hfree g (hs hg)⟩

/-! ### Crossing to the `OXMod` spelling of the category of `𝒪_{Spec R}`-modules

The pseudo-coherence material states strict perfection over
`Stacks.StrictlyPerfect.OXMod (Spec R).toRingedSpace`, which is the same *type* as
`(Spec R).Modules` but carries a different `Category` instance, so a `Retract` stated over one
is not syntactically a `Retract` over the other. Rebuilding it field by field is enough: the two
`Hom` types and the two compositions are definitionally equal, and a structure instance is
elaborated at default transparency. -/

/-- A retract of `𝒪_{Spec R}`-modules in the `Stacks.StrictlyPerfect.OXMod` spelling is a
retract in the `AlgebraicGeometry.Scheme.Modules` spelling, where Mathlib's `tilde` API lives. -/
public def retractModules {F H : StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace}
    (h : Retract F H) : Retract (F : (Spec R).Modules) (H : (Spec R).Modules) :=
  ⟨h.i, h.r, h.retract⟩

/-- `Stacks.AffineTilde.exists_finiteProjective_tilde_of_retract` for a retract stated in the
`Stacks.StrictlyPerfect.OXMod` spelling of the category of `𝒪_{Spec R}`-modules. -/
public theorem exists_finiteProjective_tilde_of_retract_oxMod {M : ModuleCat.{u} R}
    [Module.Finite R M] [Module.Projective R M]
    {F H : StrictlyPerfect.OXMod.{u, u} (Spec R).toRingedSpace}
    (eH : (tilde.functor R).obj M ≅ (H : (Spec R).Modules)) (h : Retract F H) :
    ∃ N : ModuleCat.{u} R, Module.Finite R N ∧ Module.Projective R N ∧
      Nonempty ((tilde.functor R).obj N ≅ (F : (Spec R).Modules)) :=
  exists_finiteProjective_tilde_of_retract eH (retractModules h)

end Stacks.AffineTilde

end

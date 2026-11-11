module

public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankExtension

/-!
# A monomorphism with locally free cokernel is locally split

Let `R` be a sheaf of rings on a site and let `ι : A ⟶ E` be a monomorphism of sheaves of
`R`-modules. If over an object `W` the cokernel `L` of `ι` is a coproduct of finitely many copies
of the structure sheaf, then `W` has a covering sieve along each member `Z ⟶ W` of which the
restriction `ι|_Z` is a split monomorphism.

This is the local splitting of the sequence `0 ⟶ A ⟶ E ⟶ L ⟶ 0` used in the proof of
`Stacks.SheafOfModules.exists_isColimitCofan_of_shortExact`: the basis sections of `L|_W` lift
locally along the epimorphism `E ⟶ L`, and over a member of the lifting sieve the lifts assemble
into a section of `E|_Z ⟶ L|_Z`, which splits the restricted short exact sequence.

## Main results

* `Stacks.SheafOfModules.exists_sieve_isSplitMono_overFunctor_map`: a monomorphism whose cokernel
  is free of finite rank over `W` is split over the members of a covering sieve of `W`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A monomorphism with locally free cokernel is locally split.** Let `ι : A ⟶ E` be a
monomorphism of sheaves of `R`-modules and suppose that over `W` its cokernel is a coproduct of
`c` copies of the structure sheaf. Then there is a covering sieve of `W` along each arrow
`h : Z ⟶ W` of which the restriction of `ι` to the slice over `Z` is a split monomorphism. -/
theorem exists_sieve_isSplitMono_overFunctor_map {A E : _root_.SheafOfModules.{w} R} (ι : A ⟶ E)
    [Mono ι] (W : C) {c : ℕ}
    (κ : Fin c → (_root_.SheafOfModules.unit (R.over W) ⟶ (cokernel ι).over W))
    (hκ : IsColimit (Cofan.mk _ κ)) :
    ∃ T : Sieve W, T ∈ J W ∧ ∀ ⦃Z : C⦄ (h : Z ⟶ W), T h →
      IsSplitMono ((_root_.SheafOfModules.overFunctor R Z).map ι) := by
  let S := ShortComplex.mk ι (cokernel.π ι) (cokernel.condition ι)
  have hS : S.ShortExact := { exact := S.exact_of_g_is_cokernel (cokernelIsCokernel ι) }
  obtain ⟨T, hT, hl⟩ := exists_sieve_lift_units (cokernel.π ι) W κ
  refine ⟨T, hT, fun Z h hh ↦ ?_⟩
  choose l hl' using hl h hh
  let F := _root_.SheafOfModules.overFunctor R Z
  have : PreservesFiniteLimits F := LocalCokernel.overFunctor_preservesFiniteLimits Z
  have : PreservesFiniteColimits F := LocalCokernel.overFunctor_preservesFiniteColimits Z
  have hS' : (S.map F).ShortExact := hS.map_of_exact F
  have hκZ := isColimitCofanOver (cokernel ι) h κ hκ
  let σ : (S.map F).X₃ ⟶ (S.map F).X₂ := Cofan.IsColimit.desc hκZ l
  have hσ : σ ≫ (S.map F).g = 𝟙 _ := by
    refine Cofan.IsColimit.hom_ext hκZ _ _ fun k ↦ ?_
    rw [← Category.assoc, Cofan.IsColimit.fac hκZ l k]
    exact (hl' k).trans (Category.comp_id _).symm
  let sp := ShortComplex.Splitting.ofExactOfSection (S.map F) hS'.exact σ hσ hS'.mono_f
  exact IsSplitMono.mk' { retraction := sp.r, id := sp.f_r }

end Stacks.SheafOfModules

end

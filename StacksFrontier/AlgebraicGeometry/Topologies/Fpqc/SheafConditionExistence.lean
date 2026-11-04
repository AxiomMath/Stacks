module

public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.SheafCondition

/-!
# The existence half of the fpqc sheaf condition

Let `F` be an algebraic space over `S`. Suppose that for every fpqc covering presieve `R` of an
object `X` of the big fppf category over `S` and every compatible family `x` of sections of `F`
on `R` there are a morphism `w : W ⟶ X` of the site generating a covering sieve of the fppf
topology and a section `a` of `F` over `W` which agrees with `x` on every commutative square

```
Y --u--> W
|        |
v        w
|        |
Z --f--> X
```

with `f` a member of `R`. Then `F` is a sheaf for the fpqc topology.

## Main results

* `AlgebraicGeometry.IsAlgebraicSpace.map_eq_map_of_compatible_section`: a section over `W`
  which agrees with a compatible family on an fpqc covering presieve satisfies the glueing
  condition for `w`, i.e. its two restrictions along any pair of morphisms into `W` which
  become equal over `X` agree.
* `AlgebraicGeometry.IsAlgebraicSpace.isAmalgamation_of_compatible_section`: a section of `F`
  over `X` whose restriction to `W` is such a section is an amalgamation of the family.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheafFor_fpqc_of_exists_compatible_section` and
  `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_exists_compatible_section`: the sheaf
  condition for one fpqc covering presieve, and the fpqc sheaf condition, from the existence
  of such a section over a morphism generating a covering sieve of the fppf topology.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_exists_compatible_section_on_etale_cover`:
  the same with `w` surjective and étale.
* `AlgebraicGeometry.IsAlgebraicSpace.isSheaf_fpqc_of_isSheafFor_refinement`: the fpqc sheaf
  condition follows from the sheaf condition for a *cofinal* system of fpqc coverings.

## References

* [Stacks Project, Tag 0APL](https://stacks.math.columbia.edu/tag/0APL)
* [Stacks Project, Tag 022H](https://stacks.math.columbia.edu/tag/022H)
* [Stacks Project, Tag 0APK](https://stacks.math.columbia.edu/tag/0APK)
* [Stacks Project, Tag 0AP9](https://stacks.math.columbia.edu/tag/0AP9)
* [Stacks Project, Tag 03FZ](https://stacks.math.columbia.edu/tag/03FZ)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

namespace IsAlgebraicSpace

/-- A section `a` of an algebraic space `F` over an object `W` of the big fppf category over `S`
which agrees, on every commutative square, with a compatible family of sections on an fpqc
covering presieve of `X` satisfies the glueing condition for `w : W ⟶ X`: any two morphisms into
`W` which become equal after composing with `w` restrict `a` to the same section. -/
theorem map_eq_map_of_compatible_section (hF : IsAlgebraicSpace B S hS F)
    {X W : BigFppfOver B S hS} {R : Presieve X}
    (hR : R ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) X)
    {x : Presieve.FamilyOfElements F R} {w : W ⟶ X} {a : F.obj (op W)}
    (ha : ∀ ⦃Y Z : BigFppfOver B S hS⦄ (u : Y ⟶ W) (f : Z ⟶ X) (hf : R f) (v : Y ⟶ Z),
      u ≫ w = v ≫ f → F.map u.op a = F.map v.op (x f hf))
    {Z : BigFppfOver B S hS} (p₁ p₂ : Z ⟶ W) (hp : p₁ ≫ w = p₂ ≫ w) :
    F.map p₁.op a = F.map p₂.op a := by
  have hbc : R.pullbackArrows (p₁ ≫ w) ∈
      Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) Z :=
    Precoverage.pullbackArrows_mem _ hR
  refine (hF.isSeparatedFor_fpqc hbc).ext ?_
  rintro P g ⟨Zf, f, hf⟩
  rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp,
    ha (pullback.snd f (p₁ ≫ w) ≫ p₁) f hf (pullback.fst f (p₁ ≫ w))
      (by rw [Category.assoc]; exact pullback.condition.symm),
    ha (pullback.snd f (p₁ ≫ w) ≫ p₂) f hf (pullback.fst f (p₁ ≫ w))
      (by rw [Category.assoc, ← hp]; exact pullback.condition.symm)]

/-- A section of a presheaf `F` over `X` whose restriction along `w : W ⟶ X` agrees, on every
commutative square, with a family of sections on a presieve `R` of `X` is an amalgamation of
that family, provided `F` is a sheaf for the fppf topology of the big fppf category over `S` and
`w` generates a covering sieve of that topology. -/
theorem isAmalgamation_of_compatible_section
    (hFsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) F)
    {X W : BigFppfOver B S hS} {R : Presieve X} {x : Presieve.FamilyOfElements F R} {w : W ⟶ X}
    (hw : Sieve.generate (Presieve.singleton w) ∈ BigFppfOver.topology B S hS X)
    {a : F.obj (op W)}
    (ha : ∀ ⦃Y Z : BigFppfOver B S hS⦄ (u : Y ⟶ W) (f : Z ⟶ X) (hf : R f) (v : Y ⟶ Z),
      u ≫ w = v ≫ f → F.map u.op a = F.map v.op (x f hf))
    {t : F.obj (op X)} (ht : F.map w.op t = a) :
    x.IsAmalgamation t := by
  intro Z f hf
  refine (hFsheaf _ ((BigFppfOver.topology B S hS).pullback_stable f hw)).isSeparatedFor.ext ?_
  rintro Y g ⟨W', u, w', ⟨⟩, hfac⟩
  rw [← Functor.map_comp_apply, ← op_comp, ← hfac, op_comp, Functor.map_comp_apply, ht]
  exact ha u f hf g hfac

/-- An algebraic space over `S` satisfies the sheaf condition for an fpqc covering presieve `R`
of an object `X` of the big fppf category over `S` as soon as every compatible family of
sections on `R` is, after restriction along a single morphism `w : W ⟶ X` generating a covering
sieve of the fppf topology, induced by a section over `W`. -/
theorem isSheafFor_fpqc_of_exists_compatible_section (hF : IsAlgebraicSpace B S hS F)
    {X : BigFppfOver B S hS} {R : Presieve X}
    (hR : R ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) X)
    (h : ∀ x : Presieve.FamilyOfElements F R, x.Compatible →
      ∃ (W : BigFppfOver B S hS) (w : W ⟶ X),
        Sieve.generate (Presieve.singleton w) ∈ BigFppfOver.topology B S hS X ∧
        ∃ a : F.obj (op W),
          ∀ ⦃Y Z : BigFppfOver B S hS⦄ (u : Y ⟶ W) (f : Z ⟶ X) (hf : R f) (v : Y ⟶ Z),
            u ≫ w = v ≫ f → F.map u.op a = F.map v.op (x f hf)) :
    Presieve.IsSheafFor F R := by
  have hFsheaf : Presieve.IsSheaf (BigFppfOver.topology B S hS) F :=
    (isSheaf_iff_isSheaf_of_type _ _).mp hF.isSheaf
  refine (hF.isSeparatedFor_fpqc hR).isSheafFor fun x hx => ?_
  obtain ⟨W, w, hw, a, ha⟩ := h x hx
  have hsheafW : Presieve.IsSheafFor F (Presieve.singleton w) :=
    (Presieve.isSheafFor_iff_generate _).mpr (hFsheaf _ hw)
  obtain ⟨t, ht, -⟩ := Presieve.isSheafFor_singleton.mp hsheafW a
    fun p₁ p₂ hp => hF.map_eq_map_of_compatible_section hR ha p₁ p₂ hp
  exact ⟨t, isAmalgamation_of_compatible_section hFsheaf hw ha ht⟩

/-- An algebraic space over `S` is a sheaf for the fpqc topology of the big fppf category over
`S` as soon as every compatible family of sections on an fpqc covering presieve is, after
restriction along a single morphism generating a covering sieve of the fppf topology, induced by
a section over its source. -/
theorem isSheaf_fpqc_of_exists_compatible_section (hF : IsAlgebraicSpace B S hS F)
    (h : ∀ ⦃X : BigFppfOver B S hS⦄ (R : Presieve X),
      R ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) X →
      ∀ x : Presieve.FamilyOfElements F R, x.Compatible →
      ∃ (W : BigFppfOver B S hS) (w : W ⟶ X),
        Sieve.generate (Presieve.singleton w) ∈ BigFppfOver.topology B S hS X ∧
        ∃ a : F.obj (op W),
          ∀ ⦃Y Z : BigFppfOver B S hS⦄ (u : Y ⟶ W) (f : Z ⟶ X) (hf : R f) (v : Y ⟶ Z),
            u ≫ w = v ≫ f → F.map u.op a = F.map v.op (x f hf)) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F :=
  isSheaf_fpqc_of_isSheafFor fun {_} R hR =>
    hF.isSheafFor_fpqc_of_exists_compatible_section hR (h R hR)

/-- An algebraic space over `S` is a sheaf for the fpqc topology of the big fppf category over
`S` as soon as every compatible family of sections on an fpqc covering presieve is, after
restriction along a single surjective étale morphism, induced by a section over its source. -/
theorem isSheaf_fpqc_of_exists_compatible_section_on_etale_cover
    (hF : IsAlgebraicSpace B S hS F)
    (h : ∀ ⦃X : BigFppfOver B S hS⦄ (R : Presieve X),
      R ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) X →
      ∀ x : Presieve.FamilyOfElements F R, x.Compatible →
      ∃ (W : BigFppfOver B S hS) (w : W ⟶ X),
        Surjective ((BigFppfOver.toScheme B S hS).map w) ∧
        Etale ((BigFppfOver.toScheme B S hS).map w) ∧
        ∃ a : F.obj (op W),
          ∀ ⦃Y Z : BigFppfOver B S hS⦄ (u : Y ⟶ W) (f : Z ⟶ X) (hf : R f) (v : Y ⟶ Z),
            u ≫ w = v ≫ f → F.map u.op a = F.map v.op (x f hf)) :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F := by
  refine hF.isSheaf_fpqc_of_exists_compatible_section fun {X} R hR x hx => ?_
  obtain ⟨W, w, hws, hwe, a, ha⟩ := h R hR x hx
  exact ⟨W, w, Space.sieve_generate_singleton_mem_topology_over B S hS w hws hwe, a, ha⟩

/-- An algebraic space over `S` is a sheaf for the fpqc topology of the big fppf category over
`S` as soon as every fpqc covering presieve is refined by an fpqc covering presieve for which it
is a sheaf. -/
theorem isSheaf_fpqc_of_isSheafFor_refinement (hF : IsAlgebraicSpace B S hS F)
    (h : ∀ ⦃X : BigFppfOver B S hS⦄ (R : Presieve X),
      R ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) X →
      ∃ R' : Presieve X,
        R' ∈ Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS) X ∧
        Sieve.generate R' ≤ Sieve.generate R ∧ Presieve.IsSheafFor F R') :
    Presheaf.IsSheaf
      ((Scheme.fpqcPrecoverage.comap (BigFppfOver.toScheme B S hS)).toGrothendieck) F := by
  refine isSheaf_fpqc_of_isSheafFor fun {_} R hR => ?_
  obtain ⟨R', hR', hle, hsheaf⟩ := h R hR
  rw [Presieve.isSheafFor_iff_generate]
  refine Presieve.isSheafFor_subsieve_aux F hle
    ((Presieve.isSheafFor_iff_generate _).mp hsheaf) fun Y f _ => ?_
  rw [← Sieve.pullbackArrows_comm, ← Presieve.isSeparatedFor_iff_generate]
  exact hF.isSeparatedFor_fpqc (Precoverage.pullbackArrows_mem f hR')

end IsAlgebraicSpace

end AlgebraicGeometry

end

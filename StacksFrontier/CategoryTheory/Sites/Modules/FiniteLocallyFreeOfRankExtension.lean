module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeBiproduct
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeExtension
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank

/-!
# Extensions of finite locally free modules of fixed ranks

Let `R` be a sheaf of rings on a site and let `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` be a short exact sequence
of sheaves of `R`-modules. If `M₁` and `M₃` are finite locally free of ranks `a` and `c`, then
`M₂` is finite locally free of rank `a + c`.

The proof is the usual one. Near any object, `M₁` and `M₃` are both coproducts of copies of the
structure sheaf. The quotient map `M₂ ⟶ M₃` is an epimorphism of sheaves, so its sections lift
locally, and after refining the covering once more the finitely many basis sections of `M₃` lift
simultaneously to `M₂`. There the quotient map has a section, the sequence splits, and `M₂` is the
biproduct of the two free modules.

## Main results

* `Stacks.SheafOfModules.exists_sieve_lift_unit` and
  `Stacks.SheafOfModules.exists_sieve_lift_units`: sections of the target of an epimorphism of
  sheaves of modules, read as morphisms out of the structure sheaf, lift along a covering sieve;
  finitely many of them along one covering sieve.
* `Stacks.SheafOfModules.exists_isColimitCofan_of_shortExact`: an extension of two free modules of
  finite rank whose quotient map admits lifts of the basis is free of the sum of the ranks.
* `Stacks.SheafOfModules.exists_cover_isColimitCofan_of_shortExact`: the covering form of the
  main result, for an arbitrary sheaf of rings on an arbitrary site.
* `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank.of_shortExact`: **the middle term of an
  extension of modules of ranks `a` and `c` on a ringed site has rank `a + c`.**
* `AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_zero_of_isZero`: a zero module has
  rank `0`.

## Implementation notes

The rank is the rank clause of Stacks 0409,
`AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`, which asks for a trivializing covering
family of every object. Composites of covering families are covering by
`CategoryTheory.Sieve.ofArrows_sigma_comp_mem`, and a covering sieve is read as the covering family
of all its arrows, so no common refinement of the two trivializations has to be constructed by
hand. The sieves along which the basis sections lift are intersected one section at a time, so
the finiteness of the rank is what makes a single covering sieve suffice.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

section Lift

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A section of the target of an epimorphism lifts locally**, in the form of morphisms out of
the structure sheaf: for an epimorphism `p : M ⟶ N` and `κ : 𝒪 ⟶ N|_W`, there is a covering
sieve of `W` along each arrow `h : Z ⟶ W` of which the restriction of `κ` factors through
`p|_Z`. -/
theorem exists_sieve_lift_unit {M N : _root_.SheafOfModules.{w} R} (p : M ⟶ N) [Epi p] (W : C)
    (κ : _root_.SheafOfModules.unit (R.over W) ⟶ N.over W) :
    ∃ T : Sieve W, T ∈ J W ∧ ∀ ⦃Z : C⦄ (h : Z ⟶ W), T h →
      ∃ l : _root_.SheafOfModules.unit (R.over Z) ⟶ M.over Z,
        l ≫ p.over Z = (_root_.SheafOfModules.overMap R h).map κ ≫
          ((_root_.SheafOfModules.overFunctorMap R h).app N).hom := by
  obtain ⟨T, hT, hlift⟩ :=
    EpiMono.exists_covering_of_epi p (evalOver ((N.over W).unitHomEquiv κ))
  refine ⟨T, hT, fun Z h hh ↦ ?_⟩
  obtain ⟨t, ht⟩ := hlift h hh
  refine ⟨(M.over Z).unitHomEquiv.symm (mkOver t), ?_⟩
  apply (N.over Z).unitHomEquiv.injective
  apply evalOver_injective
  rw [_root_.SheafOfModules.unitHomEquiv_comp_apply, evalOver_sectionsMap,
    Equiv.apply_symm_apply]
  refine (congrArg (fun x ↦ (toAb M N p).app (op Z) x) (evalOver_mkOver t)).trans ?_
  refine ht.trans ?_
  exact ((N.over W).unitHomEquiv κ).property (Over.homMk h (by simp) :
    (Over.map h).obj (Over.mk (𝟙 Z)) ⟶ Over.mk (𝟙 W)).op

/-- **Finitely many sections of the target of an epimorphism lift simultaneously, locally.**
For an epimorphism `p : M ⟶ N` and finitely many `κ k : 𝒪 ⟶ N|_W`, there is one covering sieve
of `W` along each arrow `h : Z ⟶ W` of which every restriction of `κ k` factors through
`p|_Z`. -/
theorem exists_sieve_lift_units {M N : _root_.SheafOfModules.{w} R} (p : M ⟶ N) [Epi p] (W : C) :
    ∀ {n : ℕ} (κ : Fin n → (_root_.SheafOfModules.unit (R.over W) ⟶ N.over W)),
    ∃ T : Sieve W, T ∈ J W ∧ ∀ ⦃Z : C⦄ (h : Z ⟶ W), T h → ∀ k,
      ∃ l : _root_.SheafOfModules.unit (R.over Z) ⟶ M.over Z,
        l ≫ p.over Z = (_root_.SheafOfModules.overMap R h).map (κ k) ≫
          ((_root_.SheafOfModules.overFunctorMap R h).app N).hom
  | 0, _ => ⟨⊤, J.top_mem W, fun _ _ _ k ↦ k.elim0⟩
  | n + 1, κ => by
      obtain ⟨T₀, hT₀, h₀⟩ := exists_sieve_lift_unit p W (κ 0)
      obtain ⟨T', hT', h'⟩ := exists_sieve_lift_units p W (fun k ↦ κ k.succ)
      refine ⟨T₀ ⊓ T', J.intersection_covering hT₀ hT', fun Z h hh k ↦ ?_⟩
      refine Fin.cases ?_ (fun k ↦ ?_) k
      · exact h₀ h hh.1
      · exact h' h hh.2 k

end Lift

section Split

variable [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C, HasSheafify (J.over V) AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **An extension of free modules whose quotient map has a section is free of the sum of the
ranks.** Let `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` be short exact. If over `Z` the restrictions of `M₁` and
`M₃` are coproducts of `a` and `c` copies of the structure sheaf, and the `c` legs of the
second lift to `M₂|_Z`, then `M₂|_Z` is a coproduct of `a + c` copies of the structure
sheaf. -/
theorem exists_isColimitCofan_of_shortExact {S : ShortComplex (_root_.SheafOfModules.{w} R)}
    (hS : S.ShortExact) (Z : C) {a c : ℕ}
    (ι : Fin a → (_root_.SheafOfModules.unit (R.over Z) ⟶ S.X₁.over Z))
    (hι : IsColimit (Cofan.mk _ ι))
    (κ : Fin c → (_root_.SheafOfModules.unit (R.over Z) ⟶ S.X₃.over Z))
    (hκ : IsColimit (Cofan.mk _ κ))
    (l : Fin c → (_root_.SheafOfModules.unit (R.over Z) ⟶ S.X₂.over Z))
    (hl : ∀ k, l k ≫ S.g.over Z = κ k) :
    ∃ ι' : Fin (a + c) → (_root_.SheafOfModules.unit (R.over Z) ⟶ S.X₂.over Z),
      Nonempty (IsColimit (Cofan.mk _ ι')) := by
  let F := _root_.SheafOfModules.overFunctor R Z
  have : PreservesFiniteLimits F := LocalCokernel.overFunctor_preservesFiniteLimits Z
  have : PreservesFiniteColimits F := LocalCokernel.overFunctor_preservesFiniteColimits Z
  have hS' : (S.map F).ShortExact := hS.map_of_exact F
  let σ : (S.map F).X₃ ⟶ (S.map F).X₂ := Cofan.IsColimit.desc hκ l
  have hσ : σ ≫ (S.map F).g = 𝟙 _ := by
    refine Cofan.IsColimit.hom_ext hκ _ _ fun k ↦ ?_
    rw [← Category.assoc, Cofan.IsColimit.fac hκ l k]
    exact (hl k).trans (Category.comp_id (κ k)).symm
  let sp := ShortComplex.Splitting.ofExactOfSection (S.map F) hS'.exact σ hσ hS'.mono_f
  exact ⟨fun x ↦ Fin.addCases (motive := fun _ ↦ _ ⟶ S.X₁.over Z ⊞ S.X₃.over Z)
      (fun i ↦ ι i ≫ biprod.inl) (fun j ↦ κ j ≫ biprod.inr) x ≫ sp.isoBinaryBiproduct.inv,
    ⟨IsColimit.ofIsoColimit (isColimitCofanBiprod ι κ hι hκ)
      (Cocone.ext sp.isoBinaryBiproduct.symm (fun _ ↦ rfl))⟩⟩

/-- **The middle term of an extension of modules of ranks `a` and `c` has rank `a + c`**, in the
covering form: if every object has a covering family over whose members `M₁` is a coproduct of `a`
copies of the structure sheaf, and likewise `M₃` with `c` copies, then the same holds for `M₂`
with `a + c` copies.

Given `U`, a trivializing family `V i ⟶ U` of `M₃` is refined by trivializing families
`W i j ⟶ V i` of `M₁`, and these by the covering sieves of `W i j` along which the `c` legs of
`M₃|_{W i j}` lift to `M₂`; over the members of the last family the quotient map has a section,
so `M₂` splits there. -/
theorem exists_cover_isColimitCofan_of_shortExact
    {S : ShortComplex (_root_.SheafOfModules.{w} R)} (hS : S.ShortExact) {a c : ℕ}
    (h₁ : ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ i, ∃ ι : Fin a →
        (_root_.SheafOfModules.unit (R.over (V i)) ⟶ S.X₁.over (V i)),
        Nonempty (IsColimit (Cofan.mk _ ι)))
    (h₃ : ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ i, ∃ ι : Fin c →
        (_root_.SheafOfModules.unit (R.over (V i)) ⟶ S.X₃.over (V i)),
        Nonempty (IsColimit (Cofan.mk _ ι)))
    (U : C) :
    ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧ ∀ i, ∃ ι : Fin (a + c) →
        (_root_.SheafOfModules.unit (R.over (V i)) ⟶ S.X₂.over (V i)),
        Nonempty (IsColimit (Cofan.mk _ ι)) := by
  have : Epi S.g := hS.epi_g
  obtain ⟨I, V, f, hf, h3V⟩ := h₃ U
  choose κ hκ using h3V
  choose I' W g hg h1W using fun i ↦ h₁ (V i)
  choose ι hι using h1W
  let κW : ∀ i j, Fin c → (_root_.SheafOfModules.unit (R.over (W i j)) ⟶ S.X₃.over (W i j)) :=
    fun i j k ↦ (_root_.SheafOfModules.overMap R (g i j)).map (κ i k) ≫
      ((_root_.SheafOfModules.overFunctorMap R (g i j)).app S.X₃).hom
  have hκW : ∀ i j, IsColimit (Cofan.mk _ (κW i j)) :=
    fun i j ↦ isColimitCofanOver S.X₃ (g i j) (κ i) (hκ i).some
  choose T hT hl using fun i j ↦ exists_sieve_lift_units S.g (W i j) (κW i j)
  let K : ∀ i, I' i → Type (max u v) := fun i j ↦ Σ Z : C, { h : Z ⟶ W i j // T i j h }
  have hK : ∀ i j, Sieve.ofArrows (fun x : K i j ↦ x.1) (fun x ↦ x.2.1) ∈ J (W i j) :=
    fun i j ↦ J.superset_covering (fun Z h hh ↦
      Sieve.ofArrows_mk (fun x : K i j ↦ x.1) (fun x ↦ x.2.1) ⟨Z, h, hh⟩) (hT i j)
  refine ⟨Σ i, Σ j : I' i, K i j, fun x ↦ x.2.2.1, fun x ↦ (x.2.2.2.1 ≫ g x.1 x.2.1) ≫ f x.1,
    Sieve.ofArrows_sigma_comp_mem J hf
      (fun i ↦ Sieve.ofArrows_sigma_comp_mem J (hg i) (hK i)), ?_⟩
  rintro ⟨i, j, Z, h, hh⟩
  choose l hl' using hl i j h hh
  exact exists_isColimitCofan_of_shortExact hS Z _
    (isColimitCofanOver S.X₁ h (ι i j) (hι i j).some) _
    (isColimitCofanOver S.X₃ h (κW i j) (hκW i j)) l hl'

end Split

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w})

/-- **A zero module has rank `0`**: over the identity of every object it is the empty
coproduct. -/
theorem isFiniteLocallyFreeOfRank_zero_of_isZero
    {M : _root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (hM : IsZero M) :
    IsFiniteLocallyFreeOfRank X M 0 := by
  intro U
  have htop : Sieve.ofArrows (fun _ : PUnit.{max u v + 1} ↦ U) (fun _ ↦ 𝟙 U) = ⊤ :=
    Sieve.id_mem_iff_eq_top.mp (Sieve.ofArrows_mk _ _ PUnit.unit)
  have hz : IsZero (M.over U) :=
    Functor.map_isZero (_root_.SheafOfModules.overFunctor _ U) hM
  refine ⟨PUnit.{max u v + 1}, fun _ ↦ U, fun _ ↦ 𝟙 U, htop ▸ X.J.top_mem U,
    fun _ ↦ ⟨fun k ↦ k.elim0, ⟨Cofan.IsColimit.mk _ (fun t ↦ hz.isInitial.to t.pt)
      (fun _ k ↦ k.elim0) (fun _ _ _ ↦ hz.eq_of_src _ _)⟩⟩⟩

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{w}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **An extension of modules of ranks `a` and `c` has rank `a + c`.** For a short exact
sequence `0 ⟶ M₁ ⟶ M₂ ⟶ M₃ ⟶ 0` of sheaves of modules on a ringed site with `M₁` finite
locally free of rank `a` and `M₃` finite locally free of rank `c`, the middle term `M₂` is
finite locally free of rank `a + c`. -/
theorem IsFiniteLocallyFreeOfRank.of_shortExact
    {S : ShortComplex (_root_.SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (hS : S.ShortExact) {a c : ℕ} (h₁ : IsFiniteLocallyFreeOfRank X S.X₁ a)
    (h₃ : IsFiniteLocallyFreeOfRank X S.X₃ c) : IsFiniteLocallyFreeOfRank X S.X₂ (a + c) :=
  Stacks.SheafOfModules.exists_cover_isColimitCofan_of_shortExact hS h₁ h₃

end AlgebraicGeometry.RingedSite

end

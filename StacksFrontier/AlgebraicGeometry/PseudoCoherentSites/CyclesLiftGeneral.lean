module

public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteTypeKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.IteratedSlice
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteType
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.SingleApproximationGeneral

/-!
# Lifting a local epimorphism onto a cohomology sheaf to the cycles, on a ringed site

Let `(C, O)` be a ringed site, let `𝒦` be a complex of `O`-modules and suppose `H^p(𝒦)` is an
`O`-module of finite type. Then every object `U` of `C` carries a covering family over each
member `V` of which there are a direct summand `𝒜` of a finite free `O|_V`-module and a map
`𝒜 ⟶ Z^p(𝒦|_V)` whose composite with `Z^p(𝒦|_V) ⟶ H^p(𝒦|_V)` is an epimorphism.

Together with
`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_local_epi_homologyπ_general` this
gives the converse half of Stacks 09VA at its top nonvanishing degree: a complex of `O`-modules
with no cohomology above `p` whose `p`-th cohomology sheaf is of finite type is
`p`-pseudo-coherent.

This is the ringed-site form of
`AlgebraicGeometry.RingedSpace.exists_local_epi_comp_homologyπ_of_isFiniteType_homology` of
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/CyclesLift.lean`. Two shrinkings happen, as
there. Finite type gives a covering family `{Y i}` of the final object of the site together
with an epimorphism `O|_{Y i}^{⊕n} ⟶ H^p(𝒦)|_{Y i}` for each `i`; an arrow `V ⟶ U` factoring
through some `Y i` carries that epimorphism to `O|_V^{⊕n} ⟶ H^p(𝒦)|_V` by exactness of
restriction, and Stacks 08FN lifts it through the epimorphism `Z^p(𝒦)|_V ⟶ H^p(𝒦)|_V` over the
members of a covering sieve of `V`. The two coverings are composed with `Sieve.bind` and
transitivity.

## Main results

* `Stacks.CyclesLiftSite.exists_epi_comp_homologyπ_of_iso`: for an exact functor `F`, a map
  into `F(Z^p 𝒦)` which is epimorphic onto `F(H^p 𝒦)` becomes, along any identification of the
  degreewise image of `𝒦` with a complex `ℒ`, a map into `Z^p(ℒ)` epimorphic onto `H^p(ℒ)`.
* `Stacks.CyclesLiftSite.exists_coveringSieve_lift_free`: **Stacks 08FN** in the form consumed
  here — a map out of a finite-free retract lifts through a locally surjective map after
  restriction to the members of a covering sieve.
* `AlgebraicGeometry.RingedSite.exists_local_epi_comp_homologyπ_of_isFiniteType_homology_general`:
  the local lift itself.
* `AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_isFiniteType_homology_general`
  and
  `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_Q_of_isFiniteType_homology_general`: the
  resulting criterion for `p`-pseudo-coherence, for a complex and for the object of `D(O)` it
  represents.

## Implementation notes

**What had to be duplicated, and why.** Three groups of declarations used here are not
available at the universes or the visibility this file needs, and the files holding them are
owned elsewhere.

* The `homologyπ` square of an exact functor,
  `CategoryTheory.ShortComplex.epi_comp_homologyπ_map` and its two consequences in
  `StacksFrontier/AlgebraicGeometry/PseudoCoherent/CyclesLift.lean`, is stated for two abelian
  categories *at the same object and morphism universes*. Sheaves of `O`-modules on a site
  `C : Type u` with `Category.{v} C` have their morphisms in `Type (max u w)`, while sheaves of
  `O|_V`-modules on the slice have theirs in `Type (max u v w)`; the two differ as soon as
  `v > u`, so restriction to a slice is not a functor to which those statements apply. They are
  restated here with independent universes, with their proofs unchanged.
* Stacks 08FN is available as `AlgebraicGeometry.RingedSite.exists_coveringSieve_lift`, but
  only at module universe `0`, and as the `private`
  `exists_coveringSieve_lift_of_locallySurjective` of
  `StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/LocalNullHomotopy.lean`, which
  is at a free module universe and in exactly the form needed here. The latter is restated and
  reproved below, together with the two `private` declarations it rests on,
  `IsFiniteFreeRetract` and its comparison with `IsDirectSummandOfFiniteFree`.
  `Stacks.SheafOfModules.LocalCokernel.exists_local_lift` is *not* a substitute: it requires the
  epimorphism to have a finite free source, whereas the epimorphism lifted through here is
  `Z^p(𝒦)|_V ⟶ H^p(𝒦)|_V`, whose source is an arbitrary module.

**Where the conclusion of 08FN lives.** The lifting statement produces its lift over a slice of
the site it is applied to; applied to the slice `C/V`, that is the iterated slice
`(C/V)/(Over.mk g)`. It is carried down to `C/W` by `Stacks.SheafOfModules.sliceBackward`,
whose composite with restriction to the iterated slice *is* restriction along `g` —
`Stacks.SheafOfModules.overFunctor_comp_sliceBackward`, an equality of functors. Only the
isomorphism form `sliceBackwardIso` is used below, through its naturality: the equality itself
is a `rfl` which does not elaborate within the heartbeat budget at the level of a single
morphism.

## References

* [Stacks Project, Lemma 20.49.2 (Tag 09VA)](https://stacks.math.columbia.edu/tag/09VA)
* [Stacks Project, Tag 08FN](https://stacks.math.columbia.edu/tag/08FN)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u₁ v₁ u₂ v₂ u v w d

namespace Stacks.CyclesLiftSite

/-! ### The `homologyπ` square of an exact functor, at independent universes -/

section Square

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]

omit [Abelian B] in
/-- Being an epimorphism transports along an equality of morphisms. Used rather than `rw`: the
morphisms compared below are composites in which the cycles of a complex appear both as
`HomologicalComplex.cycles` and as the cycles of the degree-`p` short complex, two spellings
that are definitionally but not syntactically equal. -/
theorem epi_of_eq' {M N : B} {f g : M ⟶ N} (hfg : f = g) (hg : Epi g) : Epi f := by
  cases hfg; exact hg

/-- **The comparison `(F S).cycles ≅ F (S.cycles)` is compatible with `toCycles`.** Both sides
become `F S.f` after composing with the monomorphism `(F S).iCycles`. -/
theorem toCycles_comp_mapCyclesIso_hom (S : ShortComplex A) (F : A ⥤ B)
    [F.PreservesZeroMorphisms] [F.PreservesLeftHomologyOf S] :
    (S.map F).toCycles ≫ (S.mapCyclesIso F).hom = F.map S.toCycles := by
  rw [← Iso.eq_comp_inv, ← cancel_mono ((S.map F).iCycles), ShortComplex.toCycles_i,
    Category.assoc, ← ShortComplex.mapCyclesIso_hom_iCycles, Iso.inv_hom_id_assoc, ← F.map_comp,
    ShortComplex.toCycles_i, ShortComplex.map_f]

/-- **The `homologyπ` square of an exact functor, in the form a lifting argument needs.** Let
`F` be an exact functor and `S` a short complex. A map `c` into the cycles of `F S` is
epimorphic onto the homology of `F S` as soon as the corresponding map into `F (S.cycles)` is
epimorphic onto `F (S.homology)`. -/
theorem epi_comp_homologyπ_map (S : ShortComplex A) (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] {Z : B} (c : Z ⟶ (S.map F).cycles)
    (h : Epi (c ≫ (S.mapCyclesIso F).hom ≫ F.map S.homologyπ)) :
    Epi (c ≫ (S.map F).homologyπ) := by
  have hw : (S.map F).toCycles ≫ (S.mapCyclesIso F).hom ≫ F.map S.homologyπ = 0 := by
    rw [← Category.assoc, toCycles_comp_mapCyclesIso_hom S F, ← F.map_comp,
      ShortComplex.toCycles_comp_homologyπ, F.map_zero]
  have hcB := CokernelCofork.mapIsColimit _ S.homologyIsCokernel F
  have hχ : F.map S.toCycles ≫ (S.mapCyclesIso F).inv ≫ (S.map F).homologyπ = 0 := by
    rw [← toCycles_comp_mapCyclesIso_hom S F, Category.assoc, Iso.hom_inv_id_assoc,
      ShortComplex.toCycles_comp_homologyπ]
  obtain ⟨ψ', hψ'⟩ := CokernelCofork.IsColimit.desc' hcB
    ((S.mapCyclesIso F).inv ≫ (S.map F).homologyπ) hχ
  simp only [CokernelCofork.map_π, Cofork.π_ofπ] at hψ'
  set ψ := (S.map F).descHomology ((S.mapCyclesIso F).hom ≫ F.map S.homologyπ) hw with hψ
  have hsq : (S.map F).homologyπ ≫ ψ = (S.mapCyclesIso F).hom ≫ F.map S.homologyπ :=
    ShortComplex.π_descHomology _ _ _
  have h1 : ψ ≫ ψ' = 𝟙 _ := by
    refine Cofork.IsColimit.hom_ext (S.map F).homologyIsCokernel ?_
    simp only [Cofork.π_ofπ]
    rw [← Category.assoc, hsq, Category.assoc, hψ', Iso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm
  have h2 : ψ' ≫ ψ = 𝟙 _ := by
    refine Cofork.IsColimit.hom_ext hcB ?_
    simp only [CokernelCofork.map_π, Cofork.π_ofπ]
    rw [← Category.assoc, hψ', Category.assoc, hsq, Iso.inv_hom_id_assoc]
    exact (Category.comp_id _).symm
  have hiso : IsIso ψ := ⟨ψ', h1, h2⟩
  have hepi : Epi ((c ≫ (S.map F).homologyπ) ≫ ψ) := by
    rw [Category.assoc, hsq]
    exact h
  have hfac : c ≫ (S.map F).homologyπ = ((c ≫ (S.map F).homologyπ) ≫ ψ) ≫ inv ψ := by simp
  rw [hfac]
  exact epi_comp _ _

/-- `Stacks.CyclesLiftSite.epi_comp_homologyπ_map` for the degreewise image of a cochain complex
under an exact functor. -/
theorem epi_comp_homologyπ_mapHomologicalComplex (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (M : CochainComplex A ℤ) (p : ℤ)
    {Z : B} (c : Z ⟶ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).cycles p)
    (h : Epi (c ≫ ((M.sc p).mapCyclesIso F).hom ≫ F.map (M.homologyπ p))) :
    Epi (c ≫ ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M).homologyπ p) :=
  epi_comp_homologyπ_map (M.sc p) F c h

/-- **An epimorphism onto `F(H^p 𝒦)` through `F(Z^p 𝒦)` becomes, along any identification of
the degreewise image of `𝒦` with a complex `ℒ`, an epimorphism onto `H^p(ℒ)` through
`Z^p(ℒ)`.** -/
theorem exists_epi_comp_homologyπ_of_iso (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (M : CochainComplex A ℤ)
    (L : CochainComplex B ℤ)
    (θ : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M ≅ L) (p : ℤ) {Z : B}
    (c : Z ⟶ F.obj (M.cycles p)) (h : Epi (c ≫ F.map (M.homologyπ p))) :
    ∃ c' : Z ⟶ L.cycles p, Epi (c' ≫ L.homologyπ p) := by
  have heq := (Category.assoc c ((M.sc p).mapCyclesIso F).inv
      (((M.sc p).mapCyclesIso F).hom ≫ F.map (M.homologyπ p))).trans
    (congrArg (fun g => c ≫ g)
      (Iso.inv_hom_id_assoc ((M.sc p).mapCyclesIso F) (F.map (M.homologyπ p))))
  have hA := epi_comp_homologyπ_mapHomologicalComplex F M p
    (c ≫ ((M.sc p).mapCyclesIso F).inv) (epi_of_eq' heq h)
  refine ⟨(c ≫ ((M.sc p).mapCyclesIso F).inv) ≫ HomologicalComplex.cyclesMap θ.hom p,
    epi_of_eq' ?_
      (@epi_comp _ _ _ _ _ _ hA (HomologicalComplex.homologyMap θ.hom p) inferInstance)⟩
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun g => (c ≫ ((M.sc p).mapCyclesIso F).inv) ≫ g)
      (HomologicalComplex.homologyπ_naturality θ.hom p).symm).trans
        (Category.assoc _ _ _).symm)

end Square

/-! ### Stacks 08FN at a free module universe -/

section Lift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/-- `E` is a retract of a finite coproduct of copies of the structure sheaf, witnessed by an
explicit colimit cofan. This says exactly what `IsDirectSummandOfFiniteFree` says — see
`Stacks.CyclesLiftSite.isFiniteFreeRetract_of_isDirectSummandOfFiniteFree` — but names no
sheafification functor, so that it may be stated over an arbitrary slice. -/
def IsFiniteFreeRetract (R : Sheaf J RingCat.{w}) (E : SheafOfModules.{w} R) : Prop :=
  ∃ (n : ℕ) (cf : Cofan fun _ : Fin n => SheafOfModules.unit R) (_ : IsColimit cf)
    (j : E ⟶ cf.pt) (r : cf.pt ⟶ E), j ≫ r = 𝟙 E

/-- A direct summand of a finite free module is a retract of a finite coproduct of copies of
the structure sheaf: take the tautological cofan with point `O^{⊕n}`, reindexed along
`Equiv.ulift` because `IsDirectSummandOfFiniteFree` indexes the finite free module by
`ULift.{w} (Fin n)`. -/
theorem isFiniteFreeRetract_of_isDirectSummandOfFiniteFree
    {R : Sheaf J RingCat.{w}} [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] {E : SheafOfModules.{w} R}
    (hE : IsDirectSummandOfFiniteFree R E) : IsFiniteFreeRetract R E := by
  obtain ⟨n, j, r, hjr⟩ := (isDirectSummandOfFiniteFree_iff_free R E).mp hE
  let c0 := SheafOfModules.freeCofan (R := R) (ULift.{w} (Fin n))
  have hc0 : IsColimit c0 := SheafOfModules.isColimitFreeCofan (R := R) (ULift.{w} (Fin n))
  let cf : Cofan fun _ : Fin n => SheafOfModules.unit R :=
    Cofan.mk c0.pt fun i => c0.inj (ULift.up i)
  exact ⟨n, cf,
    Cofan.IsColimit.mk cf (fun t => Cofan.IsColimit.desc hc0 fun i => t.inj i.down)
      (fun t i => by simp [cf])
      (fun t m hm => Cofan.IsColimit.hom_ext hc0 _ _ fun i => by simpa [cf] using hm i.down),
    j, r, hjr⟩

/-- A finite free module `O^{⊕n}` is a direct summand of a finite free module. -/
private theorem isDirectSummandOfFiniteFree_free (R : Sheaf J RingCat.{w})
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}] (n : ℕ) :
    IsDirectSummandOfFiniteFree R (SheafOfModules.free (R := R) (ULift.{w} (Fin n))) :=
  (isDirectSummandOfFiniteFree_iff_free R _).mpr ⟨n, 𝟙 _, 𝟙 _, Category.id_comp _⟩

/-- **Stacks 08FN**, in the form consumed here: the modules live on `C` itself rather than on a
slice, the finite-free hypothesis is `Stacks.CyclesLiftSite.IsFiniteFreeRetract`, and local
surjectivity of `p` is a hypothesis rather than a consequence of `Epi p`.

The lift is produced one coordinate at a time: the composite `q = r ≫ e` out of the coproduct
is `n` sections of `F` over `U`, each lifts through `p` on a covering sieve because `p` is
locally surjective, the intersection of those `n` sieves is covering, and over it the chosen
lifts assemble by the universal property of the coproduct. -/
theorem exists_coveringSieve_lift_free
    (R : Sheaf J RingCat.{w}) (U : C)
    (E F G : SheafOfModules.{w} R) (e : E ⟶ F) (p : G ⟶ F)
    (hE : IsFiniteFreeRetract R E)
    (hLS : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map p.val)) :
    ∃ S : Sieve U, S ∈ J U ∧
      ∀ {V : C} (f : V ⟶ U), S f →
        ∃ l : E.over V ⟶ G.over V, l ≫ p.over V = e.over V := by
  classical
  obtain ⟨n, cf, hcf, j, r, hjr⟩ := hE
  let q : cf.pt ⟶ F := r ≫ e
  let s : Fin n → F.sections := fun k => F.unitHomEquiv (cf.inj k ≫ q)
  let image : Fin n → Sieve U := fun k =>
    Presheaf.imageSieve ((PresheafOfModules.toPresheaf R.obj).map p.val)
      ((s k).val (Opposite.op U))
  have himage : ∀ k : Fin n, image k ∈ J U :=
    fun k => hLS.imageSieve_mem ((s k).val (Opposite.op U))
  let Scov : Sieve U := ⨅ k : Fin n, image k
  have hScov : Scov ∈ J U :=
    Stacks.SheafOfModules.FiniteTypeKernel.iInf_mem J image himage
  refine ⟨Scov, hScov, ?_⟩
  intro V f hf
  have hle : ∀ k : Fin n, Scov ≤ image k := fun k => iInf_le image k
  let a : Fin n → (G.val).obj (Opposite.op V) := fun k =>
    Classical.choose (show image k f from hle k f hf)
  have ha : ∀ k : Fin n,
      p.val.app (Opposite.op V) (a k) =
        F.val.map f.op ((s k).val (Opposite.op U)) :=
    fun k => Classical.choose_spec (show image k f from hle k f hf)
  let Gf := G.over V
  let pF : Gf ⟶ F.over V := p.over V
  let t : Fin n → Gf.sections := fun k =>
    PresheafOfModules.sectionsMk
      (fun Y => G.val.map Y.unop.hom.op (a k)) (by
        intro Y Z gg
        show G.val.map (gg.unop.left.op) (G.val.map (Y.unop.hom.op) (a k)) =
          G.val.map (Z.unop.hom.op) (a k)
        rw [← G.val.map_comp_apply, ← op_comp, Over.w gg.unop])
  let H := SheafOfModules.overFunctor R V
  have hHcoprod : PreservesColimit
      (Discrete.functor fun _ : Fin n => SheafOfModules.unit R) H := by
    have : PreservesFiniteLimits H :=
      Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V
    have : PreservesBiproduct (fun _ : Fin n => SheafOfModules.unit R) H :=
      preservesBiproduct_of_preservesProduct _
    exact preservesCoproduct_of_preservesBiproduct _
  let c := H.mapCocone cf
  have hc : IsColimit c := isColimitOfPreserves H hcf
  let η : SheafOfModules.unit (R.over V) ≅ H.obj (SheafOfModules.unit R) := Iso.refl _
  let d : Cofan (fun _ : Fin n => H.obj (SheafOfModules.unit R)) :=
    Cofan.mk Gf (fun i => η.inv ≫ Gf.unitHomEquiv.symm (t i))
  let kk : cf.pt.over V ⟶ Gf := hc.desc d
  have hk : kk ≫ p.over V = q.over V := by
    apply hc.hom_ext
    intro i
    show c.ι.app i ≫ kk ≫ pF = c.ι.app i ≫ q.over V
    apply (cancel_epi η.hom).1
    have hsections : SheafOfModules.sectionsMap pF (t i.as) =
        (F.over V).unitHomEquiv (η.hom ≫ c.ι.app i ≫ q.over V) := by
      apply PresheafOfModules.sections_ext
      intro Y
      show p.val.app (Opposite.op Y.unop.left)
        (G.val.map Y.unop.hom.op (a i.as)) = _
      rw [PresheafOfModules.naturality_apply, ha i.as]
      show F.val.map Y.unop.hom.op
        (F.val.map f.op ((s i.as).val (Opposite.op U))) = _
      have hsection := (s i.as).property Y.unop.hom.op
      rw [← (s i.as).property f.op] at hsection
      have hsection' :
          (ConcreteCategory.hom (F.val.map Y.unop.hom.op))
              ((ConcreteCategory.hom (F.val.map f.op)) ((s i.as).val (Opposite.op U))) =
            (s i.as).val (Opposite.op Y.unop.left) := hsection
      have hgen : (s i.as).val (Opposite.op Y.unop.left) =
          (η.hom ≫ c.ι.app i ≫ q.over V).val.app Y
            (1 : (R.over V).obj.obj Y) := by
        simp [s, η, c, H, Cofan.inj, SheafOfModules.overFunctor,
          SheafOfModules.pushforward, Functor.mapCocone_ι_app]
        rfl
      exact hsection'.trans hgen
    calc
      η.hom ≫ c.ι.app i ≫ kk ≫ pF =
          (F.over V).unitHomEquiv.symm (SheafOfModules.sectionsMap pF (t i.as)) := by
        calc
          η.hom ≫ c.ι.app i ≫ kk ≫ pF = η.hom ≫ d.ι.app i ≫ pF :=
            congrArg (fun m => η.hom ≫ m ≫ pF) (hc.fac d i)
          _ = η.hom ≫ (η.inv ≫ Gf.unitHomEquiv.symm (t i.as)) ≫ pF := by rfl
          _ = (F.over V).unitHomEquiv.symm
                (SheafOfModules.sectionsMap pF (t i.as)) := by
            dsimp only [Gf]
            simp only [Category.assoc, Iso.hom_inv_id_assoc]
            exact SheafOfModules.unitHomEquiv_symm_comp (t i.as) pF
      _ = (F.over V).unitHomEquiv.symm
          ((F.over V).unitHomEquiv (η.hom ≫ c.ι.app i ≫ q.over V)) := congrArg _ hsections
      _ = η.hom ≫ c.ι.app i ≫ q.over V := (F.over V).unitHomEquiv.symm_apply_apply _
  refine ⟨j.over V ≫ kk, ?_⟩
  rw [Category.assoc, hk]
  show (SheafOfModules.overFunctor R V).map (j ≫ r ≫ e) =
    (SheafOfModules.overFunctor R V).map e
  rw [← Category.assoc, hjr, Category.id_comp]

end Lift

/-! ### Carrying a lift down from an iterated slice -/

section Down

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

/-- **A factorisation over the iterated slice `(C/V)/(Over.mk g)` is a factorisation over the
slice `C/W`.** Transport from the iterated slice composed with restriction to it *is*
restriction along `g`, so the statement is the same one read through
`Stacks.SheafOfModules.sliceBackwardIso` and its naturality. -/
theorem exists_lift_overMap_of_lift_iteratedSlice {V W : C} (g : W ⟶ V)
    {E F G : SheafOfModules.{w} (R.over V)} (e : E ⟶ F) (q : G ⟶ F)
    (l : (SheafOfModules.overFunctor.{w} (R.over V) (Over.mk g)).obj E ⟶
      (SheafOfModules.overFunctor.{w} (R.over V) (Over.mk g)).obj G)
    (hl : l ≫ (SheafOfModules.overFunctor.{w} (R.over V) (Over.mk g)).map q =
      (SheafOfModules.overFunctor.{w} (R.over V) (Over.mk g)).map e) :
    ∃ c : (SheafOfModules.overMap.{w} R g).obj E ⟶ (SheafOfModules.overMap.{w} R g).obj G,
      c ≫ (SheafOfModules.overMap.{w} R g).map q = (SheafOfModules.overMap.{w} R g).map e := by
  have hnatq := (Stacks.SheafOfModules.sliceBackwardIso.{w} R g).hom.naturality q
  have hnate := (Stacks.SheafOfModules.sliceBackwardIso.{w} R g).hom.naturality e
  simp only [Functor.comp_map] at hnatq hnate
  refine ⟨(Stacks.SheafOfModules.sliceBackwardIso.{w} R g).inv.app E ≫
    (Stacks.SheafOfModules.sliceBackward.{w} R g).map l ≫
    (Stacks.SheafOfModules.sliceBackwardIso.{w} R g).hom.app G, ?_⟩
  have h1 : (Stacks.SheafOfModules.sliceBackward.{w} R g).map l ≫
        (Stacks.SheafOfModules.sliceBackwardIso.{w} R g).hom.app G ≫
          (SheafOfModules.overMap.{w} R g).map q =
      (Stacks.SheafOfModules.sliceBackwardIso.{w} R g).hom.app E ≫
        (SheafOfModules.overMap.{w} R g).map e := by
    rw [← hnatq, ← Category.assoc, ← Functor.map_comp, hl]
    exact hnate
  simp only [Category.assoc]
  rw [h1, ← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]

/-- **Restriction to the slice over `V` and then along `g : W ⟶ V` is restriction to the slice
over `W`**, in the form used to reindex an epimorphism onto a cohomology sheaf. -/
theorem epi_comp_overFunctorMap {V W : C} (g : W ⟶ V) {M N : SheafOfModules.{w} R} (q : M ⟶ N)
    {A : SheafOfModules.{w} (R.over W)}
    (c : A ⟶ (SheafOfModules.overMap.{w} R g).obj ((SheafOfModules.overFunctor.{w} R V).obj M))
    (hc : Epi (c ≫ (SheafOfModules.overMap.{w} R g).map
      ((SheafOfModules.overFunctor.{w} R V).map q))) :
    Epi ((c ≫ (SheafOfModules.overFunctorMap.{w} R g).hom.app M) ≫
      (SheafOfModules.overFunctor.{w} R W).map q) := by
  have hnat := (SheafOfModules.overFunctorMap.{w} R g).hom.naturality q
  simp only [Functor.comp_map] at hnat
  have hiso : IsIso ((SheafOfModules.overFunctorMap.{w} R g).hom.app N) :=
    ((SheafOfModules.overFunctorMap.{w} R g).app N).isIso_hom
  rw [Category.assoc, ← hnat, ← Category.assoc]
  have := hc
  exact epi_comp _ _

end Down

end Stacks.CyclesLiftSite

namespace AlgebraicGeometry.RingedSite

section Main

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

-- Restriction to a slice of the site preserves finite limits and finite colimits, and
-- restriction along an arrow of the site preserves finite colimits. All three are `local
-- instance`s of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`, so the
-- declarations are imported and only the instance attribute is re-enabled here.
attribute [local instance] ovFunctorLimits ovFunctorColimits overMapColimits

/-- **A local epimorphism onto `H^p(𝒦)` lifts to the cycles, on a ringed site.** Let `𝒦` be a
complex of `O`-modules whose `p`-th cohomology sheaf is of finite type. Then every object `U` of
the site carries a covering family over each member `V` of which there are a direct summand `𝒜`
of a finite free `O|_V`-module and a map `𝒜 ⟶ Z^p(𝒦|_V)` whose composite with
`Z^p(𝒦|_V) ⟶ H^p(𝒦|_V)` is an epimorphism.

Finite type gives a covering family `{Y i}` of the final object together with an epimorphism
`O|_{Y i}^{⊕n} ⟶ H^p(𝒦)|_{Y i}`; an arrow `f : V ⟶ U` of `Sieve.ofObjects Y U` factors through
some `Y i`, and restriction along that factorisation — which is exact and carries finite free
modules to finite free modules — turns the epimorphism into `O|_V^{⊕n} ⟶ H^p(𝒦)|_V`. Stacks
08FN lifts it through `Z^p(𝒦)|_V ⟶ H^p(𝒦)|_V` over the members of a covering sieve of `V`,
with the lift living on the iterated slice; `Stacks.SheafOfModules.sliceBackward` brings it down
and `Stacks.CyclesLiftSite.exists_epi_comp_homologyπ_of_iso` puts it in the asked-for form. -/
theorem exists_local_epi_comp_homologyπ_of_isFiniteType_homology_general
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (p : ℤ)
    (hft : (K.homology p).IsFiniteType) (U : X.C) :
    ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        ∃ A : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V),
          IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) A ∧
          ∃ c : A ⟶ (X.restrictComplex K V).cycles p,
            Epi (c ≫ (X.restrictComplex K V).homologyπ p) := by
  classical
  obtain ⟨I₀, Y, hY, hgen⟩ :=
    (Stacks.SheafOfModules.isFiniteType_iff_exists_cover_finite_generators
      (K.homology p)).mp hft
  have hS₀ : Sieve.generate (Sieve.ofObjects Y U).arrows ∈ X.J U := by
    rw [Sieve.generate_sieve]; exact hY U
  -- restriction along an arrow of the site preserves epimorphisms
  have hmapEpi : ∀ {V W : X.C} (g : W ⟶ V) {M N : SheafOfModules.{w}
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)} (f : M ⟶ N), Epi f →
      Epi ((SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).map f) :=
    fun {_ _} g {_ _} f hf =>
      let := Stacks.SheafOfModules.LocalCokernel.overMap_preservesEpimorphisms
        (R := Stacks.SheafOfModules.Tensor.ringSheaf X.O) g
      let := hf
      inferInstance
  have key : ∀ (V : X.C) (f : V ⟶ U), (Sieve.ofObjects Y U).arrows f →
      ∃ T : Sieve V, T ∈ X.J V ∧ ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
        ∃ A : SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W),
          IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) A ∧
          ∃ c : A ⟶ (X.restrictComplex K W).cycles p,
            Epi (c ≫ (X.restrictComplex K W).homologyπ p) := by
    intro V f hf
    obtain ⟨i, ⟨b⟩⟩ := (Sieve.mem_ofObjects_iff Y f).mp hf
    obtain ⟨σ, hσ⟩ := hgen i
    have hfinI : Finite σ.I := hσ.finite
    -- the epimorphism `O|_{Y i}^{⊕n} ⟶ H^p(𝒦)|_{Y i}`, with the finite index type of a finite
    -- free module in place of the index type of the generating family
    obtain ⟨n, u, hu_epi⟩ : ∃ (n : ℕ) (u : SheafOfModules.free
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (Y i)) (ULift.{w} (Fin n)) ⟶
        (K.homology p).over (Y i)), Epi u := by
      have efree :
          SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (Y i))
              (ULift.{w} (Fin (Nat.card σ.I))) ≅
            SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (Y i))
              σ.I :=
        (SheafOfModules.freeFunctor
            (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (Y i))).mapIso
          (Equiv.ulift.trans (Finite.equivFin σ.I).symm).toIso
      refine ⟨Nat.card σ.I, efree.hom ≫ σ.π, ?_⟩
      let : IsIso efree.hom := efree.isIso_hom
      exact epi_comp _ _
    -- restrict it along `b : V ⟶ Y i`
    obtain ⟨ub, hub_epi⟩ : ∃ ub : SheafOfModules.free
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
        (ULift.{w} (Fin n)) ⟶ (K.homology p).over V, Epi ub := by
      have h1 := hmapEpi b u hu_epi
      exact ⟨(SheafOfModules.mapFreeIso
          (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) b)
          (ULift.{w} (Fin n))
          (SheafOfModules.overMapUnitIso (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            b)).hom ≫
        (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) b).map u ≫
        (SheafOfModules.overFunctorMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) b).hom.app
          (K.homology p),
        let := h1
        epi_comp _ _⟩
    -- the epimorphism `Z^p(𝒦)|_V ⟶ H^p(𝒦)|_V` and its local surjectivity
    have hπ : Epi (K.homologyπ p) := inferInstanceAs (Epi ((K.sc p).homologyπ))
    have hpV_epi :
        Epi ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).map
          (K.homologyπ p)) :=
      let := Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesEpimorphisms
        (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) V
      let := hπ
      inferInstance
    have hLS : Presheaf.IsLocallySurjective (X.J.over V)
        ((PresheafOfModules.toPresheaf
            ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V).obj).map
          ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).map
            (K.homologyπ p)).val) :=
      let := hpV_epi
      Stacks.SheafOfModules.LocalCokernel.locallySurjective_of_epi _
    -- `O|_V^{⊕n}` is a direct summand of a finite free module, hence a finite free retract
    have hfreeDS : IsDirectSummandOfFiniteFree
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
          (ULift.{w} (Fin n))) :=
      Stacks.CyclesLiftSite.isDirectSummandOfFiniteFree_free _ n
    -- Stacks 08FN on the slice `C/V`
    obtain ⟨S₂, hS₂, hlift⟩ := Stacks.CyclesLiftSite.exists_coveringSieve_lift_free
      ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) (Over.mk (𝟙 V))
      (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
        (ULift.{w} (Fin n)))
      ((K.homology p).over V) ((K.cycles p).over V) ub
      ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).map
        (K.homologyπ p))
      (Stacks.CyclesLiftSite.isFiniteFreeRetract_of_isDirectSummandOfFiniteFree hfreeDS) hLS
    refine ⟨Sieve.overEquiv (Over.mk (𝟙 V)) S₂, (X.J.mem_over_iff S₂).mp hS₂, ?_⟩
    intro W g hg
    -- the arrow of `S₂` attached to `g`
    have harr : S₂.arrows
        (Over.homMk (U := Over.mk g) (V := Over.mk (𝟙 V)) g (by simp)) := by
      have h1 : S₂ (Over.homMk (U := Over.mk (g ≫ (Over.mk (𝟙 V)).hom)) g) :=
        (Sieve.overEquiv_iff S₂ g).mp hg
      have h2 := S₂.downward_closed h1
        (Over.homMk (U := Over.mk g) (V := Over.mk (g ≫ (Over.mk (𝟙 V)).hom))
          (𝟙 W) (by simp))
      have h3 : (Over.homMk (U := Over.mk g)
            (V := Over.mk (g ≫ (Over.mk (𝟙 V)).hom)) (𝟙 W) (by simp)) ≫
          (Over.homMk (U := Over.mk (g ≫ (Over.mk (𝟙 V)).hom)) g :
            _ ⟶ Over.mk (𝟙 V)) =
          Over.homMk (U := Over.mk g) (V := Over.mk (𝟙 V)) g (by simp) := by
        apply Over.OverMorphism.ext
        simp
      rwa [h3] at h2
    obtain ⟨l, hl⟩ := hlift (Over.homMk (U := Over.mk g) (V := Over.mk (𝟙 V)) g (by simp)) harr
    -- bring the lift down from the iterated slice to the slice over `W`
    obtain ⟨c₀, hc₀eq⟩ := Stacks.CyclesLiftSite.exists_lift_overMap_of_lift_iteratedSlice
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g ub
      ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).map
        (K.homologyπ p))
      l hl
    have hc₀epi : Epi (c₀ ≫
        (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).map
          ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).map
            (K.homologyπ p))) := by
      rw [hc₀eq]
      exact hmapEpi g ub hub_epi
    -- reindex the target along `(O|_V)|_g = O|_W`
    refine ⟨(SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).obj
        (SheafOfModules.free (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)
          (ULift.{w} (Fin n))), ?_, ?_⟩
    · exact IsDirectSummandOfFiniteFree.of_iso
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)
        (SheafOfModules.mapFreeIso
          (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g)
          (ULift.{w} (Fin n))
          (SheafOfModules.overMapUnitIso (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            g)).symm
        (Stacks.CyclesLiftSite.isDirectSummandOfFiniteFree_free _ n)
    · exact Stacks.CyclesLiftSite.exists_epi_comp_homologyπ_of_iso
        (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W) K
        (X.restrictComplex K W) (Iso.refl _) p
        (c₀ ≫ (SheafOfModules.overFunctorMap.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g).hom.app (K.cycles p))
        (Stacks.CyclesLiftSite.epi_comp_overFunctorMap
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g (K.homologyπ p) c₀ hc₀epi)
  refine ⟨(Sieve.bind (Sieve.ofObjects Y U).arrows (fun V f hf => (key V f hf).choose)).arrows,
    ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    refine X.J.transitive hS₀ _ ?_
    intro Z h hh
    obtain ⟨Z', q, f₀, hf₀, rfl⟩ := hh
    refine X.J.superset_covering ?_
      (X.J.pullback_stable q ((key Z' f₀ hf₀).choose_spec.1))
    intro Y' q' hq'
    exact ⟨Z', q' ≫ q, f₀, hf₀, hq', by simp⟩
  · intro W h hmem
    obtain ⟨Z, q, f₀, hf₀, hq, rfl⟩ := hmem
    exact (key Z f₀ hf₀).choose_spec.2 q hq

/-- **A complex of `O`-modules with no cohomology above `p` whose `p`-th cohomology sheaf is of
finite type is `p`-pseudo-coherent.** This is
`AlgebraicGeometry.RingedSite.isPseudoCoherentComplexFrom_of_local_epi_homologyπ_general` fed
with
`AlgebraicGeometry.RingedSite.exists_local_epi_comp_homologyπ_of_isFiniteType_homology_general`,
and it is the base case `p = m` of the induction of the converse half of Stacks 09VA. -/
theorem isPseudoCoherentComplexFrom_of_isFiniteType_homology_general
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (p : ℤ)
    (hvanish : ∀ j : ℤ, p < j → IsZero (K.homology j))
    (hft : (K.homology p).IsFiniteType) :
    X.IsPseudoCoherentComplexFrom K p :=
  isPseudoCoherentComplexFrom_of_local_epi_homologyπ_general X K p hvanish
    (exists_local_epi_comp_homologyπ_of_isFiniteType_homology_general X K p hft)

/-- The object of `D(O)` represented by a complex with no cohomology above `p` whose `p`-th
cohomology sheaf is of finite type is `p`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_Q_of_isFiniteType_homology_general
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) (p : ℤ)
    (hvanish : ∀ j : ℤ, p < j → IsZero (K.homology j))
    (hft : (K.homology p).IsFiniteType) :
    X.IsPseudoCoherentFrom (DerivedCategory.Q.obj K) p :=
  ⟨K, isPseudoCoherentComplexFrom_of_isFiniteType_homology_general X K p hvanish hft,
    ⟨Iso.refl _⟩⟩

end Main

end AlgebraicGeometry.RingedSite

end

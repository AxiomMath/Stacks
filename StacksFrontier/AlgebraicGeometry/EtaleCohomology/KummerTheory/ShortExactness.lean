module

public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Kummer complex and a criterion for its short exactness

For a natural number `n` and a category of schemes carrying a topology for which the
multiplicative presheaf is a sheaf, the Kummer complex is
`0 ⟶ μ_n ⟶ 𝐆_m ⟶ 𝐆_m ⟶ 0`, with first map the inclusion of the roots of unity and second map
the `n`-th power map. This file records the complex and the criterion for it to be short exact.

## Main definitions

* `AlgebraicGeometry.kummerSequence` is the Kummer complex of abelian sheaves.

## Main results

* `AlgebraicGeometry.unitsPresheaf_comp_forget_isSheaf_fpqc` — the units of global functions on
  the schemes over a base form an fpqc sheaf of sets.
* `AlgebraicGeometry.kummerSequence_shortExact_of_isLocallySurjective` — the complex is short
  exact as soon as the `n`-th power map is locally surjective for the topology.

## Implementation notes

The sheaf category of abelian groups at the universe of the schemes need not be abelian, since
the site is one universe larger; the criterion therefore transports the complex along the
universe-lifting functor on abelian groups, argues there, and descends the conclusion, using
that this functor is fully faithful, preserves kernels and reflects epimorphisms.

## References

* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL)
* [Stacks Project, Tag 040N](https://stacks.math.columbia.edu/tag/040N)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v

/-- The underlying presheaf of sets of the presheaf of units of global functions on the schemes
over `S` is an fpqc sheaf: it is represented by the multiplicative group scheme over `S`, and
the fpqc topology is subcanonical. -/
@[sga "4 IX 3.0" "partial", sga "4½ Arcata 2.2.2" "more general"]
public theorem unitsPresheaf_comp_forget_isSheaf_fpqc (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      ((unitsPresheaf (Over.forget S)) ⋙ forget AddCommGrpCat.{u}) := by
  let X : Over S := Scheme.asOver
    (multiplicativeGroupBaseChange S) S
  have hYon : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj X) :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type
      (J := Scheme.fpqcTopology.over S) (yoneda.obj X)).2 <|
      CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
        (J := Scheme.fpqcTopology.over S) (yoneda.obj X)
  have eYon : yoneda.obj X ≅
      (CategoryTheory.yonedaGrpObj X) ⋙ CategoryTheory.forget GrpCat := by
    refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
    intro Y Z f
    ext g
    rfl
  have hGrpYon : Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      ((CategoryTheory.yonedaGrpObj X) ⋙ CategoryTheory.forget GrpCat) :=
    (Presheaf.isSheaf_of_iso_iff eYon).mp hYon
  have hGlobal : Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      ((globalUnits S) ⋙ CategoryTheory.forget GrpCat) :=
    (Presheaf.isSheaf_of_iso_iff
      (Functor.isoWhiskerRight
        (baseChangePointsIsoGlobalUnits S)
        (CategoryTheory.forget GrpCat))).mp hGrpYon
  have eUnits : (globalUnits S) ⋙ CategoryTheory.forget GrpCat ≅
      (unitsPresheaf (Over.forget S)) ⋙ forget AddCommGrpCat.{u} := by
    refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
    intro Y Z f
    ext g
    rfl
  exact (Presheaf.isSheaf_of_iso_iff eUnits).mp hGlobal

attribute [-instance] CategoryTheory.sheafIsAbelian

/-- The Kummer complex of abelian sheaves: the inclusion of the kernel of the `n`-th power map
on the sheaf of units, followed by that power map. -/
@[sga "7 IX 14.3" "special case", sga "7 IX 9.4.3"]
public noncomputable def kummerSequence {C : Type v} [Category C]
    (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ) :
    ShortComplex (Sheaf J AddCommGrpCat.{u}) :=
  ShortComplex.mk (Limits.kernel.ι (powerSheaf J F h n))
    (powerSheaf J F h n) (Limits.kernel.condition _)

attribute [instance] CategoryTheory.sheafIsAbelian

/-- **The Kummer short-exactness criterion.** If the `n`-th power map on the units presheaf of a
site is locally surjective, the Kummer complex of abelian sheaves is short exact. Left
exactness is formal, because the first map is the kernel inclusion; the content is that local
surjectivity makes the second map epi and the complex exact.

The argument is run after composing with the universe-lifting functor on abelian groups, where
the sheaf category is abelian: that functor is fully faithful, preserves kernels and reflects
epimorphisms, so the cokernel of the lifted complex descends. -/
public lemma kummerSequence_shortExact_of_isLocallySurjective
    {C : Type*} [Category C] (J : GrothendieckTopology C)
    (F : C ⥤ Scheme.{u}) (hF : Presheaf.IsSheaf J (unitsPresheaf F))
    (n : ℕ)
    [EssentiallySmall.{u + 1} C]
    [J.HasSheafCompose (forget AddCommGrpCat.{u})]
    (hloc : Presheaf.IsLocallySurjective J (powerPresheaf F n)) :
    (kummerSequence J F hF n).ShortExact := by
  let S := kummerSequence J F hF n
  let : HasSheafify J AddCommGrpCat.{u + 1} :=
    hasSheafifyEssentiallySmallSite J AddCommGrpCat.{u + 1}
  let : J.HasSheafCompose (AddCommGrpCat.uliftFunctor.{u + 1, u}) := inferInstance
  let H := sheafCompose J (AddCommGrpCat.uliftFunctor.{u + 1, u})
  let : H.Faithful := inferInstance
  let : H.Full := inferInstance
  let : Functor.ReflectsEpimorphisms H := ⟨fun {X Y} f hf => by
    refine ⟨?_⟩
    intro Z g h hfg
    exact H.map_injective <| hf.left_cancellation _ _ <| by
      simpa only [Functor.map_comp] using congrArg H.map hfg
  ⟩
  let : Functor.PreservesZeroMorphisms H := by
    constructor
    intro X Y
    apply Sheaf.hom_ext
    ext U x
    rfl
  let : J.HasSheafCompose (forget AddCommGrpCat.{u + 1}) := inferInstance
  have hlocHigh : Presheaf.IsLocallySurjective J
      ((sheafToPresheaf J AddCommGrpCat.{u + 1}).map (H.map S.g)) := by
    show Presheaf.IsLocallySurjective J
      (Functor.whiskerRight S.g.hom (AddCommGrpCat.uliftFunctor.{u + 1, u}))
    refine ⟨?_⟩
    intro U x
    have hc := hloc.imageSieve_mem (x.down)
    apply J.superset_covering ?_ hc
    intro V f hf
    obtain ⟨b, hb⟩ := hf
    refine ⟨ULift.up b, ?_⟩
    show ULift.up ((powerPresheaf F n).app (Opposite.op V) b) =
      ULift.up ((unitsPresheaf F).map f.op x.down)
    rw [hb]
  let : Sheaf.IsLocallySurjective (H.map S.g) := hlocHigh
  have : Epi (H.map S.g) := Sheaf.epi_of_isLocallySurjective _
  have hker : IsLimit (KernelFork.ofι S.f S.zero) := by
    show IsLimit (KernelFork.ofι
      (Limits.kernel.ι (powerSheaf J F hF n)) _)
    exact kernelIsKernel _
  let : PreservesLimitsOfShape WalkingParallelPair
      (H ⋙ sheafToPresheaf J AddCommGrpCat.{u + 1}) := by
    let : PreservesLimitsOfShape WalkingParallelPair
        (sheafToPresheaf J AddCommGrpCat.{u}) := inferInstance
    show PreservesLimitsOfShape WalkingParallelPair
      (sheafToPresheaf J AddCommGrpCat.{u} ⋙
        (Functor.whiskeringRight Cᵒᵖ AddCommGrpCat AddCommGrpCat).obj
          AddCommGrpCat.uliftFunctor.{u + 1, u})
    infer_instance
  let : ReflectsLimitsOfShape WalkingParallelPair
      (sheafToPresheaf J AddCommGrpCat.{u + 1}) := inferInstance
  let : PreservesLimitsOfShape WalkingParallelPair H :=
    preservesLimitsOfShape_of_reflects_of_preserves H
      (sheafToPresheaf J AddCommGrpCat.{u + 1})
  have : Abelian (Sheaf J AddCommGrpCat.{u + 1}) := inferInstance
  let : NonPreadditiveAbelian (Sheaf J AddCommGrpCat.{u + 1}) :=
    Abelian.nonPreadditiveAbelian
  let : HasZeroMorphisms (Sheaf J AddCommGrpCat.{u + 1}) :=
    (Abelian.nonPreadditiveAbelian).toHasZeroMorphisms
  let highS : ShortComplex (Sheaf J AddCommGrpCat.{u + 1}) :=
    ShortComplex.mk (H.map S.f) (H.map S.g) (by
      rw [← Functor.map_comp, S.zero, Functor.map_zero])
  have hkerHigh : IsLimit (KernelFork.ofι highS.f highS.zero) := KernelFork.mapIsLimit _ hker H
  have hcokerHigh : IsColimit (CokernelCofork.ofπ highS.g highS.zero) :=
    Abelian.epiIsCokernelOfKernel (KernelFork.ofι highS.f highS.zero) hkerHigh
  let cokerMap {Z' : Sheaf J AddCommGrpCat.{u}} (k : S.X₂ ⟶ Z')
      (hk : S.f ≫ k = 0) : CokernelCofork (H.map S.f) :=
    CokernelCofork.ofπ (H.map k) (by
      rw [← Functor.map_comp, hk, Functor.map_zero])
  have hcokerLow : IsColimit (CokernelCofork.ofπ S.g S.zero) :=
    CokernelCofork.IsColimit.ofπ S.g S.zero
      (fun {Z'} k hk => H.preimage (hcokerHigh.desc (cokerMap k hk)))
      (by
        intro Z' k hk
        apply H.map_injective
        show H.map S.g ≫ H.map (H.preimage (hcokerHigh.desc (cokerMap k hk))) = H.map k
        calc
          H.map S.g ≫ H.map (H.preimage (hcokerHigh.desc (cokerMap k hk))) =
              H.map S.g ≫ hcokerHigh.desc (cokerMap k hk) := by rw [H.map_preimage]
          _ = H.map k := Cofork.IsColimit.π_desc hcokerHigh)
      (by
        intro Z' k hk m hm
        apply H.map_injective
        have hdesc : hcokerHigh.desc (cokerMap k hk) = H.map m := by
          apply Cofork.IsColimit.hom_ext hcokerHigh
          calc
            H.map S.g ≫ hcokerHigh.desc (cokerMap k hk) = H.map k :=
              Cofork.IsColimit.π_desc hcokerHigh
            _ = H.map S.g ≫ H.map m := by
              rw [← Functor.map_comp, hm]
        calc
          H.map m = hcokerHigh.desc (cokerMap k hk) := hdesc.symm
          _ = H.map (H.preimage (hcokerHigh.desc (cokerMap k hk))) :=
            (H.map_preimage _).symm)
  let f' : S.X₁ ⟶ S.X₁ := hker.lift (KernelFork.ofι S.f S.zero)
  have hf' : f' = 𝟙 S.X₁ := by
    apply hker.hom_ext
    simp [f']
  let zeroGrp : AddCommGrpCat.{u} := AddCommGrpCat.of (ULift.{u} PUnit)
  have hzeroGrp : IsTerminal zeroGrp :=
    IsTerminal.ofUniqueHom (fun _ => 0) (by
      intro X f
      apply AddCommGrpCat.hom_ext
      ext x)
  let : HasTerminal (Sheaf J AddCommGrpCat.{u}) :=
    IsTerminal.hasTerminal (Sheaf.isTerminalTerminal J hzeroGrp)
  let : HasZeroObject (Sheaf J AddCommGrpCat.{u}) :=
    hasZeroObject_of_hasTerminal_object
  let zeroObj : Sheaf J AddCommGrpCat.{u} := Sheaf.terminal J hzeroGrp
  have hzeroSheaf : IsZero zeroObj :=
    (Sheaf.isTerminalTerminal J hzeroGrp).isZero
  let left : S.LeftHomologyData := {
    K := S.X₁
    H := zeroObj
    i := S.f
    π := 0
    wi := S.zero
    hi := hker
    wπ := by simp
    hπ := CokernelCofork.IsColimit.ofπ (f := f') (g := (0 : S.X₁ ⟶ zeroObj))
      (by simp)
      (fun {_} k hk => 0)
      (by
        intro Z' k hk
        simpa [hf'] using hk.symm)
      (by
        intro Z' k hk m hm
        have hk' : k = 0 := by simpa [hf'] using hk
        subst k
        exact hzeroSheaf.eq_of_src _ _)
  }
  let g' : S.X₃ ⟶ S.X₃ := hcokerLow.desc (CokernelCofork.ofπ S.g S.zero)
  have hg' : g' = 𝟙 S.X₃ := by
    apply Cofork.IsColimit.hom_ext hcokerLow
    simp [g']
  let right : S.RightHomologyData := {
    Q := S.X₃
    H := zeroObj
    p := S.g
    ι := 0
    wp := S.zero
    hp := hcokerLow
    wι := by simp
    hι := KernelFork.IsLimit.ofι (f := g') (g := (0 : zeroObj ⟶ S.X₃))
      (by simp [hg'])
      (fun {_} k hk => 0)
      (by
        intro W' k hk
        have hk' : k = 0 := by simpa [hg'] using hk
        simp [hk'])
      (by intro W' k hk m hm; exact hzeroSheaf.eq_of_tgt _ _)
  }
  let hdata : S.HomologyData := {
    left := left
    right := right
    iso := Iso.refl zeroObj
    comm := by simp [left, right, S.zero]
  }
  have hleftZero : IsZero left.H := hzeroSheaf
  have hExact : S.Exact := (hdata.exact_iff).2 hleftZero
  have hmono : Mono S.f := by
    show Mono (Limits.kernel.ι (powerSheaf J F hF n))
    infer_instance
  have : Epi S.g := H.epi_of_epi_map (by infer_instance)
  exact ShortComplex.ShortExact.mk' hExact hmono inferInstance

end AlgebraicGeometry

end

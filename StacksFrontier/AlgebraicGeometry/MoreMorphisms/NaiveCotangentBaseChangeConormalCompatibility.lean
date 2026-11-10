module

public import StacksFrontier.AlgebraicGeometry.ConormalComparison.DefiningIdealConormalBridge
public import StacksFrontier.AlgebraicGeometry.Conormal.SplitCotangentFibre
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.CoborderDifferentialsStalk
public import StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.SchemeShortExact
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.NaiveCotangentPulledImmersionFormallySmooth

/-!
# Naturality of the first arrow of the conormal sequence, and `H^{-1}(NL_{X/Y})`

Let

```
Z' --i'--> X'
|          |
f          k
v          v
Z  --i---> X
```

be a commutative square of schemes with `i` and `i'` immersions, lying over a commutative square
`k ≫ p = p' ≫ g` of structure morphisms `p : X ⟶ S`, `p' : X' ⟶ S'`. The first arrows
`𝒞_{Z/X} ⟶ i^*Ω_{X/S}` and `𝒞_{Z'/X'} ⟶ i'^*Ω_{X'/S'}` of the conormal sequences of
[Stacks Project, Tag 01UZ] are compatible with the canonical map `f^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of
[Stacks Project, Tag 01R4] and with the map `f^*i^*Ω_{X/S} ⟶ i'^*Ω_{X'/S'}` induced by the
canonical map `k^*Ω_{X/S} ⟶ Ω_{X'/S'}` of [Stacks Project, Tag 01UV]: the square

```
f^*𝒞_{Z/X} ------> f^*i^*Ω_{X/S}
    |                    |
    v                    v
 𝒞_{Z'/X'} ------> i'^*Ω_{X'/S'}
```

commutes. Both composites carry the class of a local section `a` of the ideal of `Z` in `X` to
`1 ⊗ d(k^♯ a)`. This is the compatibility the proof of [Stacks Project, Tag 0FV9] uses, for the
base change of a factorization through a smooth morphism, to see that the kernel of the
surjection `(g')^*𝒞_{X/P} ⟶ 𝒞_{X'/P'}` lies in the kernel of the pulled-back first arrow, the
right-hand vertical map being an isomorphism there by [Stacks Project, Tag 01V0].

The file also records the identification `H^{-1}(NL_{X/Y}) ≅ Ker(𝒞_{X/P} ⟶ i^*Ω_{P/Y})` for a
morphism `f = i ≫ h` with `i` an immersion and `h` formally smooth, read off the zig-zag of
[Stacks Project, Tag 0FV4] in the same way as its pulled-back version
`Stacks.NaiveCotangentPulledImmersion.pulledComplexHomologyNegOneIso`; these are the two rows
the proof of [Stacks Project, Tag 0FV9] compares.

## Main definitions

* `Stacks.ConormalSequenceRight.pullbackSquareDifferentialsMap`: the map
  `f^*i^*Ω_{X/S} ⟶ i'^*Ω_{X'/S'}` of the square.
* `Stacks.NaiveCotangentPulledImmersion.presentationHomologyNegOneIso` and
  `Stacks.NaiveCotangentPulledImmersion.naiveCotangentHomologyNegOneIso`:
  `H^{-1}(NL_{X/Y}) ≅ Ker(𝒞_{X/P} ⟶ i^*Ω_{P/Y})`.

## Main results

* `Stacks.ConormalSequenceRight.conormalDifferential_canonicalConormalQuotientMap`: the first
  arrow carries the conormal class of a local section `a` of the ideal sheaf of `i` to
  `1 ⊗ d a`.
* `Stacks.ConormalSequenceRight.hom_ext_canonicalConormalQuotientMap`: a morphism out of the
  conormal sheaf is determined by its values on these classes.
* `Stacks.ConormalSequenceRight.immersionConormalSheafMap_comp_conormalDifferential`: **the
  square commutes.**
* `Stacks.NaiveCotangentPulledImmersion.homologyMap_comp_presentationHomologyNegOneIso`: the
  identification of `H^{-1}(NL_{X/Y})` is the one induced by the chain maps of the zig-zag.
* `Stacks.NaiveCotangentPulledImmersion.kernelιCompIsoOfKernelιComp`: restricting a morphism to
  the kernel of a second one does not change its kernel when its kernel is killed by the second.

## Implementation notes

The first arrow `Stacks.ConormalSequenceRight.conormalDifferential` is defined on the conormal
sheaf presented through the sectionwise ideal of the closed factor of `i`, while the canonical
map `Stacks.Immersion.immersionConormalSheafMap` of [Stacks Project, Tag 01R4] is defined on the
presentation through the categorical kernel; the square is stated through the identification
`Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge` of the two, which is the one the
assembly of [Stacks Project, Tag 0FV4] uses.

The square is checked after transposing along `f^* ⊣ f_*`, on the conormal classes of local
sections of the ideal sheaf of `i` in `X`, which determine a morphism out of the conormal sheaf
because their germs exhaust every stalk. On such a class both composites are computed on
sections: the left one by the pinning of the first arrow of `i` and the units of the pullback
pseudofunctor, the right one by the affine description of the map of
[Stacks Project, Tag 01R4] (`Stacks.Conormal.conormalClass_homEquiv_immersionConormalSheafMap`)
and the pinning of the first arrow of `i'`.

## References

* [Stacks Project, Tag 01UZ](https://stacks.math.columbia.edu/tag/01UZ)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 0FV4](https://stacks.math.columbia.edu/tag/0FV4)
* [Stacks Project, Tag 0FV9](https://stacks.math.columbia.edu/tag/0FV9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite RingedSpaceModuleAdjunction
open TopologicalSpace
open Stacks.AlgebraicGeometry.RegularIdealSheaf
open Stacks.ClosedImmersion Stacks.Immersion

universe u

noncomputable section

namespace Stacks.ConormalSequenceRight

section Pinning

variable {Z X S : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (p : X ⟶ S)

/-- The identification of the two presentations of the conormal sheaf carries the conormal class
of a section of the categorical ideal of the closed factor to the conormal class of the
corresponding section of the sectionwise ideal. -/
theorem conormalSheafBridge_inv_unit (V : Opens i.coborderRange.toScheme)
    (s : (Stacks.Conormal.Sites.idealSheafLift i).val.obj (op V)) :
    (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv.val.app
        (op (i.liftCoborder ⁻¹ᵁ V))
        (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (Stacks.Conormal.Sites.idealSheafLift i)).val.app (op V) s) =
      (conormalComparison i).val.app (op V)
        ((Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).inv.val.app (op V) s) := by
  have h := congr($((modulePullbackPushforwardAdjunction
    i.liftCoborder.toLRSHom.toShHom).unit.naturality
      (Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).inv).val.app (op V) s)
  exact h.symm

/-- **The first arrow on the conormal class of a section of the ideal of the closed factor**: it
is `1 ⊗ d s`, moved onto `i^*Ω_{X/S}` by
`Stacks.ConormalSequenceRight.coborderPullbackDifferentialsIso`. -/
theorem conormalDifferential_conormalSheafBridge_inv_unit (V : Opens i.coborderRange.toScheme)
    (s : (Stacks.Conormal.Sites.idealSheafLift i).val.obj (op V)) :
    ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
        conormalDifferential i p).val.app (op (i.liftCoborder ⁻¹ᵁ V))
        (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (Stacks.Conormal.Sites.idealSheafLift i)).val.app (op V) s) =
      (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p)) ≫
          (Scheme.Modules.pushforward i.liftCoborder).map
            (coborderPullbackDifferentialsIso i p).hom).val.app (op V)).hom
        ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d
          (Stacks.Conormal.idealSection i.liftCoborder V s)) := by
  have h1 := conormalSheafBridge_inv_unit i V s
  have h2 := congr($(conormalComparison_comp_conormalDifferential i p).val.app (op V)
    ((Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).inv.val.app (op V) s))
  have h3 : ((Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).inv.val.app (op V) s).1 =
      Stacks.Conormal.idealSection i.liftCoborder V s :=
    congr($(Stacks.Conormal.DefiningIdealBridge.idealSheafBridge_inv_comp_ι i).val.app (op V) s)
  refine Eq.trans (congrArg ((conormalDifferential i p).val.app (op (i.liftCoborder ⁻¹ᵁ V))) h1) ?_
  refine h2.trans ?_
  refine (conormalDifferentialTranspose_val_app i p (op V) _).trans ?_
  exact congrArg (fun a => (((Scheme.Modules.pullbackPushforwardAdjunction i.liftCoborder).unit.app
            (Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p)) ≫
          (Scheme.Modules.pushforward i.liftCoborder).map
            (coborderPullbackDifferentialsIso i p).hom).val.app (op V)).hom
        ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d a)) h3

/-- For a morphism `θ` out of the relative differentials of the coborder neighbourhood, the germ
at `z` of `θ (d a)` only depends on the germ of `a` at the image of `z`. -/
theorem germ_coborder_d_eq {N : Z.Modules}
    (θ : Scheme.Hom.relativeDifferentials (i.coborderRange.ι ≫ p) ⟶
      (Scheme.Modules.pushforward i.liftCoborder).obj N)
    (z : Z) {U₁ U₂ : Opens i.coborderRange.toScheme} (h₁ : i.liftCoborder.base z ∈ U₁)
    (h₂ : i.liftCoborder.base z ∈ U₂) (a₁ : Γ(i.coborderRange.toScheme, U₁))
    (a₂ : Γ(i.coborderRange.toScheme, U₂))
    (hgerm : i.coborderRange.toScheme.presheaf.germ U₁ _ h₁ a₁ =
      i.coborderRange.toScheme.presheaf.germ U₂ _ h₂ a₂) :
    TopCat.Presheaf.germ (C := Ab.{u}) N.val.presheaf (i.liftCoborder ⁻¹ᵁ U₁) z h₁
        ((θ.val.app (op U₁)).hom
          ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d a₁)) =
      TopCat.Presheaf.germ (C := Ab.{u}) N.val.presheaf (i.liftCoborder ⁻¹ᵁ U₂) z h₂
        ((θ.val.app (op U₂)).hom
          ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d a₂)) := by
  obtain ⟨V, hV, ι₁, ι₂, heq⟩ := i.coborderRange.toScheme.presheaf.germ_eq _ h₁ h₂ a₁ a₂ hgerm
  have key : ∀ {U : Opens i.coborderRange.toScheme} (ιU : V ⟶ U)
      (a : Γ(i.coborderRange.toScheme, U)),
      N.val.presheaf.map ((Opens.map i.liftCoborder.base).map ιU).op
          ((θ.val.app (op U)).hom
            ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d a)) =
        (θ.val.app (op V)).hom
          ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d
            (i.coborderRange.toScheme.presheaf.map ιU.op a)) := by
    intro U ιU a
    have hd := (Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d_map ιU.op a
    have hn := θ.val.naturality ιU.op
    refine Eq.trans ?_ (congrArg (θ.val.app (op V)).hom hd).symm
    exact (ConcreteCategory.congr_hom hn _).symm
  refine (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) N.val.presheaf
    ((Opens.map i.liftCoborder.base).map ι₁) z hV _).symm.trans ?_
  refine Eq.trans (congrArg _ (key ι₁ a₁)) ?_
  refine Eq.trans ?_ (TopCat.Presheaf.germ_res_apply (C := Ab.{u}) N.val.presheaf
    ((Opens.map i.liftCoborder.base).map ι₂) z hV _)
  refine Eq.trans ?_ (congrArg _ (key ι₂ a₂)).symm
  exact congrArg (fun a => TopCat.Presheaf.germ (C := Ab.{u}) N.val.presheaf _ z hV
    ((θ.val.app (op V)).hom
      ((Scheme.Hom.universalRelativeDerivation (i.coborderRange.ι ≫ p)).d a))) heq

/-- **The first arrow on the conormal class of a section of the ideal sheaf of `i`**: it is
`1 ⊗ d a`. The class is the image under `Stacks.Immersion.canonicalConormalQuotientMap` of a
section `a` of the ideal sheaf of `i` itself, in the ambient scheme rather than in the coborder
neighbourhood; the two descriptions are matched on germs. -/
theorem conormalDifferential_canonicalConormalQuotientMap (A : X.Opens)
    (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op A)) :
    ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
        conormalDifferential i p).val.app (op (i ⁻¹ᵁ A))
        ((canonicalConormalQuotientMap i).val.app (op A) y) =
      (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (Scheme.Hom.relativeDifferentials p)).val.app (op A)).hom
        ((Scheme.Hom.universalRelativeDerivation p).d (Stacks.Conormal.idealSection i A y)) := by
  refine TopCat.Presheaf.section_ext
    (⟨((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf,
      ((Scheme.Modules.pullback i).obj
        (Scheme.Hom.relativeDifferentials p)).isSheaf⟩ : TopCat.Sheaf Ab.{u} Z)
    (i ⁻¹ᵁ A) _ _ fun z hz => ?_
  have hw := Stacks.Conormal.coborderStalkEquiv_mem_ker i z _
    (Stacks.Conormal.germ_idealSection_mem_ker_stalkMap i z A hz y)
  obtain ⟨V, hzV, s, hgerm⟩ := exists_germ_eq_of_mem_ker i.liftCoborder z _ hw
  let s' := (Stacks.Conormal.DefiningIdealBridge.idealSheafBridge i).hom.val.app (op V) s
  have hs' : Stacks.Conormal.idealSection i.liftCoborder V s' = s.1 :=
    Stacks.Conormal.DefiningIdealBridge.idealSection_idealSheafBridge_hom i V s
  have hq : TopCat.Presheaf.germ (C := Ab.{u}) (Stacks.Conormal.conormalSheaf i).val.presheaf
        (i ⁻¹ᵁ A) z hz ((canonicalConormalQuotientMap i).val.app (op A) y) =
      TopCat.Presheaf.germ (C := Ab.{u}) (Stacks.Conormal.conormalSheaf i).val.presheaf
        (i.liftCoborder ⁻¹ᵁ V) z hzV
        (((modulePullbackPushforwardAdjunction i.liftCoborder.toLRSHom.toShHom).unit.app
          (Stacks.Conormal.Sites.idealSheafLift i)).val.app (op V) s') := by
    refine (Stacks.Conormal.conormalSheafStalkEquivCotangent i z).injective ?_
    refine (Stacks.Conormal.germ_canonicalConormalQuotientMap i z A hz y).trans ?_
    refine Eq.trans ?_ (Stacks.Conormal.conormalSheafStalkEquivCotangent_germ i z V hzV s').symm
    refine congrArg (Ideal.toCotangent _) (Subtype.ext ?_)
    exact hgerm.symm.trans (congrArg _ hs'.symm)
  have hmem := Stacks.Conormal.mem_coborder_preimage i z A hz
  have hgermA : i.coborderRange.toScheme.presheaf.germ V (i.liftCoborder.base z) hzV
        (Stacks.Conormal.idealSection i.liftCoborder V s') =
      i.coborderRange.toScheme.presheaf.germ (i.coborderRange.ι ⁻¹ᵁ A)
        (i.liftCoborder.base z) hmem
        ((i.coborderRange.ι.app A).hom (Stacks.Conormal.idealSection i A y)) :=
    (congrArg _ hs').trans (hgerm.trans
      (Stacks.Conormal.coborderStalkEquiv_germ i z A hz hmem _))
  refine Eq.trans (stalkAb_map_germ _ z (i ⁻¹ᵁ A) hz _).symm ?_
  refine Eq.trans (congrArg ((stalkAb Z z).map _) hq) ?_
  refine Eq.trans (stalkAb_map_germ _ z (i.liftCoborder ⁻¹ᵁ V) hzV _) ?_
  refine Eq.trans (congrArg (TopCat.Presheaf.germ (C := Ab.{u})
    ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)).val.presheaf
    (i.liftCoborder ⁻¹ᵁ V) z hzV) (conormalDifferential_conormalSheafBridge_inv_unit i p V s')) ?_
  refine Eq.trans (germ_coborder_d_eq i p _ z hzV hmem _ _ hgermA) ?_
  exact coborderPullbackDifferentialsIso_germ i p A _ z hz hmem

end Pinning

/-- Every element of a stalk of the conormal sheaf is the germ of a canonical class. -/
theorem exists_eq_germ_canonicalConormalQuotientMap {Z X : Scheme.{u}} (f : Z ⟶ X)
    [IsImmersion f] (z : Z)
    (m : ToType ((stalkAb Z z).obj (Stacks.Conormal.conormalSheaf f : Z.Modules))) :
    ∃ (A : X.Opens) (hA : z ∈ f ⁻¹ᵁ A)
      (y : (idealSheaf f.toLRSHom.toShHom).val.obj (op A)),
      m = TopCat.Presheaf.germ (C := Ab.{u}) (Stacks.Conormal.conormalSheaf f).val.presheaf
        (f ⁻¹ᵁ A) z hA ((canonicalConormalQuotientMap f).val.app (op A) y) := by
  obtain ⟨w, hw⟩ := Ideal.toCotangent_surjective (RingHom.ker (f.liftCoborder.stalkMap z).hom)
    (Stacks.Conormal.conormalSheafStalkEquivCotangent f z m)
  have hc : (Stacks.Conormal.coborderStalkEquiv f z).inv.hom w.1 ∈
      RingHom.ker (f.stalkMap z).hom := by
    rw [RingHom.mem_ker, ← Stacks.Conormal.stalkMap_coborderStalkEquiv f z,
      Iso.inv_hom_id_apply (Stacks.Conormal.coborderStalkEquiv f z) w.1]
    exact w.2
  obtain ⟨A, hA, sj, hsj⟩ := exists_germ_eq_of_mem_ker f z _ hc
  obtain ⟨y, hyeq⟩ := exists_idealSheaf_section_of_app_eq_zero f.toLRSHom.toShHom A sj.1 sj.2
  refine ⟨A, hA, y, (Stacks.Conormal.conormalSheafStalkEquivCotangent f z).injective ?_⟩
  refine Eq.trans hw.symm (Eq.trans ?_
    (Stacks.Conormal.germ_canonicalConormalQuotientMap f z A hA y).symm)
  refine congrArg (Ideal.toCotangent _) (Subtype.ext ?_)
  refine Eq.symm (Eq.trans (congrArg (fun c => (Stacks.Conormal.coborderStalkEquiv f z).hom.hom
    ((X.presheaf.germ A (f.base z) hA) c)) hyeq) ?_)
  exact (congrArg (fun c => (Stacks.Conormal.coborderStalkEquiv f z).hom.hom c) hsj).trans
    (Iso.inv_hom_id_apply (Stacks.Conormal.coborderStalkEquiv f z) w.1)

/-- Maps out of the conormal sheaf are determined by the germs of their values on canonical
classes. -/
theorem hom_ext_canonicalConormalQuotientMap {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    {N : Z.Modules} {a b : (Stacks.Conormal.conormalSheaf i : Z.Modules) ⟶ N}
    (h : ∀ (A : X.Opens) (y : (idealSheaf i.toLRSHom.toShHom).val.obj (op A)) (z : Z)
      (hz : z ∈ i ⁻¹ᵁ A),
      TopCat.Presheaf.germ (C := Ab.{u}) N.val.presheaf (i ⁻¹ᵁ A) z hz
          (a.val.app (op (i ⁻¹ᵁ A)) ((canonicalConormalQuotientMap i).val.app (op A) y)) =
        TopCat.Presheaf.germ (C := Ab.{u}) N.val.presheaf (i ⁻¹ᵁ A) z hz
          (b.val.app (op (i ⁻¹ᵁ A)) ((canonicalConormalQuotientMap i).val.app (op A) y))) :
    a = b := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  refine TopCat.Presheaf.section_ext (⟨N.val.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab.{u} Z) U _ _
    fun z hz => ?_
  obtain ⟨A, hA, y, hy⟩ := exists_eq_germ_canonicalConormalQuotientMap i z
    (TopCat.Presheaf.germ (C := Ab.{u}) (Stacks.Conormal.conormalSheaf i).val.presheaf U z hz s)
  refine (stalkAb_map_germ a z U hz s).symm.trans ?_
  refine Eq.trans ?_ (stalkAb_map_germ b z U hz s)
  refine Eq.trans (congrArg ((stalkAb Z z).map a) hy) ?_
  refine Eq.trans ?_ (congrArg ((stalkAb Z z).map b) hy).symm
  refine (stalkAb_map_germ a z _ hA _).trans ?_
  refine Eq.trans ?_ (stalkAb_map_germ b z _ hA _).symm
  exact h A y z hA

/-- Transporting the pullback along an equality of morphisms carries `1 ⊗ m` to the restriction
of `1 ⊗ m`. -/
theorem pullbackCongr_hom_unit {X' P : Scheme.{u}} {f₁ f₂ : X' ⟶ P} (h : f₁ = f₂)
    (M : P.Modules) (U : P.Opens) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app (f₁ ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f₁).unit.app M).app U m) =
      ((Scheme.Modules.pullback f₂).obj M).presheaf.map (eqToHom (by rw [h])).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f₂).unit.app M).app U m) := by
  subst h
  simp [pullbackCongr_rfl_hom_app]

section SquareUnits

variable {Z X Z' X' : Scheme.{u}} (i : Z ⟶ X) (i' : Z' ⟶ X') (f : Z' ⟶ Z) (k : X' ⟶ X)
  (hcomm : i' ≫ k = f ≫ i)

/-- The comparison `f^* i^* M ⟶ i'^* N` attached to a commutative square `i' ≫ k = f ≫ i` and a
morphism `φ : k^* M ⟶ N`, on the doubly pulled-back sections: it sends `1 ⊗ 1 ⊗ m` to the
restriction of `1 ⊗ φ (1 ⊗ m)`. -/
theorem pullbackSquareMap_unit_unit {M : X.Modules} {N : X'.Modules}
    (φ : (Scheme.Modules.pullback k).obj M ⟶ N) (U : X.Opens) (m : Γ(M, U))
    (hC : f ⁻¹ᵁ (i ⁻¹ᵁ U) ≤ i' ⁻¹ᵁ (k ⁻¹ᵁ U)) :
    ((Scheme.Modules.pullbackComp f i).hom.app M ≫
        (Scheme.Modules.pullbackCongr hcomm.symm).hom.app M ≫
          (Scheme.Modules.pullbackComp i' k).inv.app M ≫
            (Scheme.Modules.pullback i').map φ).app (f ⁻¹ᵁ (i ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
            ((Scheme.Modules.pullback i).obj M)).app (i ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app U m)) =
      ((Scheme.Modules.pullback i').obj N).presheaf.map (homOfLE hC).op
        (((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app N).app (k ⁻¹ᵁ U)
          (φ.app (k ⁻¹ᵁ U)
            (((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M).app U m))) := by
  have s1 := pullbackComp_hom_app_unit_unit f i M U m
  have s2 := pullbackCongr_hom_unit hcomm.symm M U m
  have s3 : ((Scheme.Modules.pullbackComp i' k).inv.app M).app ((i' ≫ k) ⁻¹ᵁ U)
      (((Scheme.Modules.pullbackPushforwardAdjunction (i' ≫ k)).unit.app M).app U m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
          ((Scheme.Modules.pullback k).obj M)).app (k ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M).app U m) := by
    rw [← pullbackComp_hom_app_unit_unit i' k M U m]
    exact congr($((Scheme.Modules.pullbackComp i' k).hom_inv_id_app M).app ((i' ≫ k) ⁻¹ᵁ U) _)
  have s5 : ((Scheme.Modules.pullback i').map φ).app (i' ⁻¹ᵁ (k ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
          ((Scheme.Modules.pullback k).obj M)).app (k ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M).app U m)) =
      ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app N).app (k ⁻¹ᵁ U)
        (φ.app (k ⁻¹ᵁ U)
          (((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M).app U m)) := by
    have h := congrArg (fun ψ => Scheme.Modules.Hom.app ψ (k ⁻¹ᵁ U))
      ((Scheme.Modules.pullbackPushforwardAdjunction i').unit.naturality φ)
    simp only [Functor.id_obj, Functor.id_map, Functor.comp_map, Scheme.Modules.Hom.comp_app,
      Scheme.Modules.pushforward_map_app] at h
    exact (ConcreteCategory.congr_hom h _).symm
  have hcomp : ∀ x, ((Scheme.Modules.pullbackComp f i).hom.app M ≫
        (Scheme.Modules.pullbackCongr hcomm.symm).hom.app M ≫
          (Scheme.Modules.pullbackComp i' k).inv.app M ≫
            (Scheme.Modules.pullback i').map φ).app (f ⁻¹ᵁ (i ⁻¹ᵁ U)) x =
      ((Scheme.Modules.pullback i').map φ).app (f ⁻¹ᵁ (i ⁻¹ᵁ U))
        (((Scheme.Modules.pullbackComp i' k).inv.app M).app (f ⁻¹ᵁ (i ⁻¹ᵁ U))
          (((Scheme.Modules.pullbackCongr hcomm.symm).hom.app M).app (f ⁻¹ᵁ (i ⁻¹ᵁ U))
            (((Scheme.Modules.pullbackComp f i).hom.app M).app (f ⁻¹ᵁ (i ⁻¹ᵁ U)) x))) :=
    fun x => rfl
  refine (hcomp _).trans ?_
  refine Eq.trans (congrArg (fun x => ((Scheme.Modules.pullback i').map φ).app (f ⁻¹ᵁ (i ⁻¹ᵁ U))
    (((Scheme.Modules.pullbackComp i' k).inv.app M).app (f ⁻¹ᵁ (i ⁻¹ᵁ U))
      (((Scheme.Modules.pullbackCongr hcomm.symm).hom.app M).app (f ⁻¹ᵁ (i ⁻¹ᵁ U)) x))) s1) ?_
  refine Eq.trans (congrArg (fun x => ((Scheme.Modules.pullback i').map φ).app (f ⁻¹ᵁ (i ⁻¹ᵁ U))
    (((Scheme.Modules.pullbackComp i' k).inv.app M).app (f ⁻¹ᵁ (i ⁻¹ᵁ U)) x)) s2) ?_
  refine Eq.trans (congrArg (fun x => ((Scheme.Modules.pullback i').map φ).app
    (f ⁻¹ᵁ (i ⁻¹ᵁ U)) x) (PresheafOfModules.naturality_apply
      ((Scheme.Modules.pullbackComp i' k).inv.app M).val
      (eqToHom (congrArg (fun φ : Z' ⟶ X => φ ⁻¹ᵁ U) hcomm.symm)).op _)) ?_
  refine Eq.trans (congrArg (fun x => ((Scheme.Modules.pullback i').map φ).app (f ⁻¹ᵁ (i ⁻¹ᵁ U))
    (((Scheme.Modules.pullback i').obj ((Scheme.Modules.pullback k).obj M)).presheaf.map
      (eqToHom (congrArg (fun φ : Z' ⟶ X => φ ⁻¹ᵁ U) hcomm.symm)).op x)) s3) ?_
  refine Eq.trans (PresheafOfModules.naturality_apply ((Scheme.Modules.pullback i').map φ).val
    (eqToHom (congrArg (fun φ : Z' ⟶ X => φ ⁻¹ᵁ U) hcomm.symm) ≫ homOfLE (by
      change (i' ≫ k) ⁻¹ᵁ U ≤ i' ⁻¹ᵁ (k ⁻¹ᵁ U); exact le_rfl)).op _) ?_
  refine Eq.trans (congrArg _ s5) ?_
  exact congrArg (fun ι : f ⁻¹ᵁ (i ⁻¹ᵁ U) ⟶ i' ⁻¹ᵁ (k ⁻¹ᵁ U) =>
      ((Scheme.Modules.pullback i').obj N).presheaf.map ι.op
    (((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app N).app (k ⁻¹ᵁ U)
      (φ.app (k ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app M).app U m))))
    (Subsingleton.elim _ _)

end SquareUnits

section Square

variable {Z X Z' X' S S' : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i] (i' : Z' ⟶ X')
  [IsImmersion i'] (f : Z' ⟶ Z) (k : X' ⟶ X) (hcomm : i' ≫ k = f ≫ i) (p : X ⟶ S)
  (p' : X' ⟶ S') (g : S' ⟶ S) (hp : k ≫ p = p' ≫ g)

/-- The comparison `f^*(i^*Ω_{X/S}) ⟶ i'^*Ω_{X'/S'}` attached to a commutative square of
immersions over a commutative square of bases. -/
def pullbackSquareDifferentialsMap :
    (Scheme.Modules.pullback f).obj
        ((Scheme.Modules.pullback i).obj (Scheme.Hom.relativeDifferentials p)) ⟶
      (Scheme.Modules.pullback i').obj (Scheme.Hom.relativeDifferentials p') :=
  (Scheme.Modules.pullbackComp f i).hom.app _ ≫
    (Scheme.Modules.pullbackCongr hcomm.symm).hom.app _ ≫
      (Scheme.Modules.pullbackComp i' k).inv.app _ ≫
        (Scheme.Modules.pullback i').map (Scheme.Hom.relativeDifferentialsMap k p p' g hp)

/-- **The first arrow of the conormal sequence is natural.** For a commutative square
`i' ≫ k = f ≫ i` of immersions over a commutative square `k ≫ p = p' ≫ g`, the canonical map
`f^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of [Stacks Project, Tag 01R4] followed by the first arrow of `i'` is
the pullback of the first arrow of `i` followed by `pullbackSquareDifferentialsMap`. -/
theorem immersionConormalSheafMap_comp_conormalDifferential :
    (immersionConormalSheafMap i' i f k (toShHom_square hcomm) ≫
        (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i').inv ≫
          conormalDifferential i' p' :
        (Scheme.Modules.pullback f).obj (Stacks.Conormal.conormalSheaf i) ⟶ _) =
      (Scheme.Modules.pullback f).map
          ((Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫
            conormalDifferential i p) ≫
        pullbackSquareDifferentialsMap i i' f k hcomm p p' g hp := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  apply hom_ext_canonicalConormalQuotientMap i
  intro A y z hz
  refine congrArg (TopCat.Presheaf.germ (C := Ab.{u}) _ (i ⁻¹ᵁ A) z hz) ?_
  -- the section of the ideal sheaf of `i'` lying over `k^♯ y`
  have h0 : (structureSheafModuleHom i'.toLRSHom.toShHom).val.app (op (k ⁻¹ᵁ A))
      ((k.app A).hom (Stacks.Conormal.idealSection i A y)) = 0 := by
    change ((i' ≫ k).app A).hom (Stacks.Conormal.idealSection i A y) = 0
    rw [hcomm, Scheme.Hom.comp_app]
    have hy0 := Stacks.Conormal.AffineCotangent.Sections.app_idealSheaf_section_eq_zero i A y
    exact (congrArg (f.app (i ⁻¹ᵁ A)).hom hy0).trans (map_zero _)
  obtain ⟨E, hE⟩ := exists_idealSheaf_section_of_app_eq_zero i'.toLRSHom.toShHom (k ⁻¹ᵁ A) _ h0
  have hC : f ⁻¹ᵁ (i ⁻¹ᵁ A) ≤ i' ⁻¹ᵁ (k ⁻¹ᵁ A) := by
    change (f ≫ i) ⁻¹ᵁ A ≤ (i' ≫ k) ⁻¹ᵁ A
    rw [hcomm]
  let h' : (Stacks.Conormal.conormalSheaf i' : Z'.Modules) ⟶ _ :=
    (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i').inv ≫ conormalDifferential i' p'
  let g0 : (Stacks.Conormal.conormalSheaf i : Z.Modules) ⟶ _ :=
    (Stacks.Conormal.DefiningIdealBridge.conormalSheafBridge i).inv ≫ conormalDifferential i p
  let c : (Scheme.Modules.pullback f).obj (Stacks.Conormal.conormalSheaf i) ⟶
      Stacks.Conormal.conormalSheaf i' := immersionConormalSheafMap i' i f k (toShHom_square hcomm)
  -- the left-hand side
  have hL1 : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (c ≫ h')).val.app
        (op (i ⁻¹ᵁ A)) ((canonicalConormalQuotientMap i).val.app (op A) y) =
      h'.val.app (op (f ⁻¹ᵁ (i ⁻¹ᵁ A)))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ c).val.app (op (i ⁻¹ᵁ A))
          ((canonicalConormalQuotientMap i).val.app (op A) y)) :=
    congr($(Adjunction.homEquiv_naturality_right (Scheme.Modules.pullbackPushforwardAdjunction f)
      c h').val.app (op (i ⁻¹ᵁ A)) ((canonicalConormalQuotientMap i).val.app (op A) y))
  have hL2 := Stacks.Conormal.conormalClass_homEquiv_immersionConormalSheafMap i' i f k hcomm A
    (f ⁻¹ᵁ (i ⁻¹ᵁ A)) hC le_rfl y E hE
  have hres : ∀ x : (Stacks.Conormal.conormalSheaf i').val.obj (op (f ⁻¹ᵁ (i ⁻¹ᵁ A))),
      (Stacks.Conormal.conormalSheaf i').val.map (homOfLE (le_refl (f ⁻¹ᵁ (i ⁻¹ᵁ A)))).op x = x :=
    fun x => by
      rw [show (homOfLE (le_refl (f ⁻¹ᵁ (i ⁻¹ᵁ A)))) = 𝟙 _ from Subsingleton.elim _ _]
      simp
      rfl
  have hL3 := conormalDifferential_canonicalConormalQuotientMap i' p' (k ⁻¹ᵁ A) E
  have hL : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (c ≫ h')).val.app
        (op (i ⁻¹ᵁ A)) ((canonicalConormalQuotientMap i).val.app (op A) y) =
      ((Scheme.Modules.pullback i').obj (Scheme.Hom.relativeDifferentials p')).presheaf.map
        (homOfLE hC).op
        (((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
          (Scheme.Hom.relativeDifferentials p')).app (k ⁻¹ᵁ A)
          ((Scheme.Hom.universalRelativeDerivation p').d
            ((k.app A).hom (Stacks.Conormal.idealSection i A y)))) := by
    refine hL1.trans ?_
    refine Eq.trans (congrArg (h'.val.app (op (f ⁻¹ᵁ (i ⁻¹ᵁ A)))) ((hres _).symm.trans hL2)) ?_
    refine Eq.trans (PresheafOfModules.naturality_apply h'.val (homOfLE hC).op _) ?_
    refine congrArg (((Scheme.Modules.pullback i').obj
      (Scheme.Hom.relativeDifferentials p')).presheaf.map (homOfLE hC).op) (hL3.trans ?_)
    exact congrArg (fun a => (((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
          (Scheme.Hom.relativeDifferentials p')).val.app (op (k ⁻¹ᵁ A))).hom
        ((Scheme.Hom.universalRelativeDerivation p').d a)) hE
  -- the right-hand side
  let X₀ := pullbackSquareDifferentialsMap i i' f k hcomm p p' g hp
  have hR1 : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        ((Scheme.Modules.pullback f).map g0 ≫ X₀)).val.app (op (i ⁻¹ᵁ A))
        ((canonicalConormalQuotientMap i).val.app (op A) y) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ X₀).val.app (op (i ⁻¹ᵁ A))
        (g0.val.app (op (i ⁻¹ᵁ A)) ((canonicalConormalQuotientMap i).val.app (op A) y)) :=
    congr($(Adjunction.homEquiv_naturality_left (Scheme.Modules.pullbackPushforwardAdjunction f)
      g0 X₀).val.app (op (i ⁻¹ᵁ A)) ((canonicalConormalQuotientMap i).val.app (op A) y))
  have hR2 := conormalDifferential_canonicalConormalQuotientMap i p A y
  have hR3 : ∀ x, ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ X₀).val.app
        (op (i ⁻¹ᵁ A)) x =
      X₀.val.app (op (f ⁻¹ᵁ (i ⁻¹ᵁ A)))
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app _).val.app (op (i ⁻¹ᵁ A)) x) :=
    fun x => congr($(Adjunction.homEquiv_unit (Scheme.Modules.pullbackPushforwardAdjunction f) _ _
      X₀).val.app (op (i ⁻¹ᵁ A)) x)
  have hR4 := pullbackSquareMap_unit_unit i i' f k hcomm
    (Scheme.Hom.relativeDifferentialsMap k p p' g hp) A
    ((Scheme.Hom.universalRelativeDerivation p).d (Stacks.Conormal.idealSection i A y)) hC
  have hR5 : (Scheme.Hom.relativeDifferentialsMap k p p' g hp).app (k ⁻¹ᵁ A)
        (((Scheme.Modules.pullbackPushforwardAdjunction k).unit.app
          (Scheme.Hom.relativeDifferentials p)).app A
          ((Scheme.Hom.universalRelativeDerivation p).d (Stacks.Conormal.idealSection i A y))) =
      (Scheme.Hom.universalRelativeDerivation p').d
        ((k.app A).hom (Stacks.Conormal.idealSection i A y)) :=
    (congrArg (fun φ => (φ.val.app (op A)).hom
        ((Scheme.Hom.universalRelativeDerivation p).d (Stacks.Conormal.idealSection i A y)))
      (Adjunction.homEquiv_unit (Scheme.Modules.pullbackPushforwardAdjunction k) _ _
        (Scheme.Hom.relativeDifferentialsMap k p p' g hp))).symm.trans
      (Scheme.Hom.relativeDifferentialsMap_app_d (f := k) (p := p) (p' := p') g hp A _)
  refine hL.trans (Eq.symm ?_)
  refine hR1.trans ?_
  refine Eq.trans (congrArg _ hR2) ?_
  refine (hR3 _).trans ?_
  refine hR4.trans ?_
  exact congrArg (fun a => ((Scheme.Modules.pullback i').obj
    (Scheme.Hom.relativeDifferentials p')).presheaf.map (homOfLE hC).op
      (((Scheme.Modules.pullbackPushforwardAdjunction i').unit.app
        (Scheme.Hom.relativeDifferentials p')).app (k ⁻¹ᵁ A) a)) hR5

end Square

end Stacks.ConormalSequenceRight

/-! ### `H^{-1}(NL_{X/Y})` for a morphism factored through a formally smooth scheme -/

namespace Stacks.NaiveCotangentPulledImmersion

open Stacks.SheafOfModules Stacks.Sites.FreeAlgebra
open Stacks.NaiveCotangentSixTermSequence (ringedSpaceHom)

/-- **The kernel of a map restricted to the kernel of another.** If the kernel of `c : A ⟶ B` is
killed by `a : A ⟶ D`, then restricting `c` to the kernel of `a` does not change its kernel. -/
noncomputable def kernelιCompIsoOfKernelιComp {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B D : C} (a : A ⟶ D) (c : A ⟶ B) [HasKernel a] [HasKernel c]
    [HasKernel (kernel.ι a ≫ c)] (h : kernel.ι c ≫ a = 0) :
    kernel (kernel.ι a ≫ c) ≅ kernel c where
  hom := kernel.lift c (kernel.ι _ ≫ kernel.ι a) (by simp)
  inv := kernel.lift _ (kernel.lift a (kernel.ι c) h) (by simp)
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

/-- The isomorphism `kernelιCompIsoOfKernelιComp a c h`, followed by the inclusion of the kernel
of `c`, is the inclusion of the kernel of `kernel.ι a ≫ c` followed by `kernel.ι a`. -/
@[reassoc (attr := simp)]
theorem kernelιCompIsoOfKernelιComp_hom_ι {C : Type*} [Category C] [HasZeroMorphisms C]
    {A B D : C} (a : A ⟶ D) (c : A ⟶ B) [HasKernel a] [HasKernel c]
    [HasKernel (kernel.ι a ≫ c)] (h : kernel.ι c ≫ a = 0) :
    (kernelιCompIsoOfKernelιComp a c h).hom ≫ kernel.ι c = kernel.ι _ ≫ kernel.ι a :=
  kernel.lift_ι _ _ _

/-- The image of a morphism under a functor isomorphic to `F` is its image under `F`,
conjugated by the isomorphism, after its source has been replaced by an isomorphic one. -/
theorem map_eq_conj_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (e : F ≅ G)
    {A A' B : C} (β : A ≅ A') (d : A ⟶ B) :
    G.map d = ((e.app A).symm ≪≫ F.mapIso β).hom ≫ F.map (β.inv ≫ d) ≫ (e.app B).symm.inv := by
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom, Iso.symm_inv,
    Iso.app_hom, Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_assoc]
  rw [← e.inv.naturality_assoc, Iso.inv_hom_id_app, Category.comp_id]

variable {X P Y : Scheme.{u}} (i : X ⟶ P) (h : P ⟶ Y) [IsImmersion i]

/-- The degree `-1` term of `(𝒞_{X/P} ⟶ i^*Ω_{P/Y})` vanishes in degree `-2`. -/
theorem isZero_conormalDifferentialComplex_X_negTwo :
    IsZero ((Stacks.ConormalSequenceRight.conormalDifferentialComplex i h).X (-2)) :=
  Stacks.ConormalSequenceRight.conormalDifferentialComplex_isZero_X i h (-2) (by decide)
    (by decide)

/-- The comparison of the polynomial presentation with `(𝒞_{X/P} ⟶ i^*Ω_{P/Y})` is a
quasi-isomorphism for `h` formally smooth. -/
theorem quasiIso_conormalComparison (hg : Stacks.Smooth.FormallySmoothScheme h) :
    QuasiIso (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom) :=
  have := Stacks.NaiveCotangentTower.quasiIso_schemeTowerComparison i h hg
  have : IsIso (towerIso i h).hom := (towerIso i h).isIso_hom
  have : QuasiIso (towerIso i h).hom := quasiIso_of_isIso _
  quasiIso_comp _ _

/-- The comparison of [Stacks Project, Tag 08TL] induces an isomorphism on `H^{-1}`. -/
theorem isIso_homologyMap_presentationComparison :
    IsIso (HomologicalComplex.homologyMap (presentationComparison i h) (-1)) :=
  (quasiIsoAt_iff_isIso_homologyMap _ (-1)).mp
    ((Stacks.NaiveCotangentTower.quasiIso_schemePresentationComparison i h).quasiIsoAt (-1))

/-- **`H^{-1}(NL_{X/Y})` is the kernel of the first arrow `𝒞_{X/P} ⟶ i^*Ω_{P/Y}`**, in the
spelling of `NL_{X/Y}` over the iterated inverse image `i⁻¹h⁻¹𝒪_Y`, for `h` formally smooth: the
inverse of the isomorphism induced on `H^{-1}` by the comparison of [Stacks Project, Tag 08TL],
followed by the one induced by the comparison with `(𝒞_{X/P} ⟶ i^*Ω_{P/Y})`. -/
def presentationHomologyNegOneIso (hg : Stacks.Smooth.FormallySmoothScheme h) :
    (naiveCotangentComplex.{u, u, u, u} (Opens.grothendieckTopology X.toRingedSpace.carrier)
          (inverseImageBaseRing (ringedSpaceHom i) (ringedSpaceHom h)) X.toRingedSpace.sheaf
          (inverseImageFirstRingMap (ringedSpaceHom i) (ringedSpaceHom h) ≫
            ringedSpaceStructureMap (ringedSpaceHom i))).homology (-1) ≅
      kernel (Stacks.ConormalSequenceRight.conormalDifferential i h) :=
  (@asIso _ _ _ _ (HomologicalComplex.homologyMap (presentationComparison i h) (-1))
      (isIso_homologyMap_presentationComparison i h)).symm ≪≫
    @asIso _ _ _ _ (HomologicalComplex.homologyMap
      (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom) (-1))
      ((quasiIsoAt_iff_isIso_homologyMap _ (-1)).mp
        ((quasiIso_conormalComparison i h hg).quasiIsoAt (-1))) ≪≫
    homologyNegOneIsoKernel _ (isZero_conormalDifferentialComplex_X_negTwo i h) ≪≫
    kernelIsoOfEq (Stacks.ConormalSequenceRight.conormalDifferentialComplex_d_negOne_zero i h) ≪≫
    kernelConjIso _ _ _

/-- **The compatibility of `presentationHomologyNegOneIso` with the chain maps it is built
from**: precomposed with the map induced on `H^{-1}` by the comparison of
[Stacks Project, Tag 08TL], it is the map induced by the comparison with
`(𝒞_{X/P} ⟶ i^*Ω_{P/Y})`, followed by the identification of `H^{-1}` of that complex. -/
theorem homologyMap_comp_presentationHomologyNegOneIso
    (hg : Stacks.Smooth.FormallySmoothScheme h) :
    HomologicalComplex.homologyMap (presentationComparison i h) (-1) ≫
        (presentationHomologyNegOneIso i h hg).hom =
      HomologicalComplex.homologyMap
          (Stacks.NaiveCotangentTower.schemeTowerComparison i h ≫ (towerIso i h).hom) (-1) ≫
        (homologyNegOneIsoKernel _ (isZero_conormalDifferentialComplex_X_negTwo i h) ≪≫
          kernelIsoOfEq
            (Stacks.ConormalSequenceRight.conormalDifferentialComplex_d_negOne_zero i h) ≪≫
          kernelConjIso _ _ _).hom := by
  exact Iso.hom_inv_id_assoc
    (@asIso _ _ _ _ (HomologicalComplex.homologyMap (presentationComparison i h) (-1))
      (isIso_homologyMap_presentationComparison i h)) _

/-- **`H^{-1}(NL_{X/Y}) ≅ Ker(𝒞_{X/P} ⟶ i^*Ω_{P/Y})`.** Let `f : X ⟶ Y` factor as `f = i ≫ h`
with `i : X ⟶ P` an immersion and `h : P ⟶ Y` formally smooth. The degree `-1` cohomology sheaf
of `NL_{X/Y}` is the kernel of the first arrow of the conormal sequence of `i` over `Y`: the
identification of `NL_{X/Y}` with its spelling over the iterated inverse image
(`Stacks.NaiveCotangentTower.schemePresentationIso`) followed by
`presentationHomologyNegOneIso`. -/
def naiveCotangentHomologyNegOneIso {f : X ⟶ Y} (hf : f = i ≫ h)
    (hg : Stacks.Smooth.FormallySmoothScheme h) :
    (Scheme.naiveCotangentComplex f).homology (-1) ≅
      kernel (Stacks.ConormalSequenceRight.conormalDifferential i h) :=
  eqToIso (congrArg (fun m : X ⟶ Y ↦ (Scheme.naiveCotangentComplex m).homology (-1)) hf) ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-1)).mapIso
      (Stacks.NaiveCotangentTower.schemePresentationIso i h) ≪≫
    presentationHomologyNegOneIso i h hg

end Stacks.NaiveCotangentPulledImmersion

end

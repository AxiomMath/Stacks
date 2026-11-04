module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Data.List.TFAE
public import Mathlib.Topology.NoetherianSpace
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.EmbeddedCharacterization
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.DenseOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.SchemeTheoreticallyDense
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support

/-!
# Scheme-theoretically dense opens and associated points

An open subscheme of a locally Noetherian scheme is scheme-theoretically dense exactly when it
contains every associated point of the scheme; equivalently, when it is topologically dense and
contains every embedded point.

## Main results

* `AlgebraicGeometry.isSchemeTheoreticallyDense_tfae` gives the three equivalent
  characterizations.

## Implementation notes

The three entries of the `List.TFAE` are respectively conditions (1), (2) and (3) of the source.
Containment of a point in the open subscheme is membership in its underlying open set.

Scheme-theoretic density is tested on affine opens: there it is injectivity of the map on global
sections, which is detected by the associated primes of the ring of functions, and these
correspond to the associated points by Stacks tag 02OK. Topological density is tested on the
generic points of the irreducible components, which are associated points by Stacks tag 05AH.

## References

* [Stacks Project, Tag 083P](https://stacks.math.columbia.edu/tag/083P)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

/-- The sections of the structure sheaf as a module over itself are the sections of the
structure sheaf. -/
private lemma unit_sections_carrier_eq {X : Scheme.{u}} (W : X.Opens) :
    (Γ(SheafOfModules.unit X.ringCatSheaf, W) : Type u) = Γ(X, W) := rfl

/-- A global section whose restriction to an open subscheme vanishes has vanishing germ at every
point of that subscheme. -/
private lemma germ_eq_zero_of_open_restriction_eq_zero {S : Scheme.{u}} (V : S.Opens) (x : S)
    (hx : x ∈ V) (a : Γ(S, ⊤)) (ha : (V.ι.appTop).hom a = 0) :
    S.presheaf.germ ⊤ x (by trivial) a = 0 := by
  let q := V.ι
  let y : V.toScheme := ⟨x, hx⟩
  have hzero : q.stalkMap y ((S.presheaf.germ ⊤ (q y) (by simp)).hom a) = 0 := by
    have ha' : (q.app ⊤).hom a = 0 := ha
    rw [Scheme.Hom.germ_stalkMap_apply]
    change (V.toScheme.presheaf.germ ⊤ y (by simp)) ((q.app ⊤).hom a) = 0
    rw [ha']
    exact map_zero _
  have hqi : Function.Injective (q.stalkMap y).hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance |>.1
  refine hqi ?_
  change q.stalkMap y ((S.presheaf.germ ⊤ (q y) (by simp)).hom a) = (q.stalkMap y).hom 0
  simpa only [map_zero] using hzero

/-- If an open contains all associated points of the scheme, then restriction of the sections of
the structure sheaf from an affine open to its intersection with that open is injective. -/
@[ega "IV 3.1.8" "special case"]
private lemma appTop_injective_of_associatedPoints_subset {X : Scheme.{u}}
    [IsLocallyNoetherian X] (W : X.Opens) (hW : IsAffineOpen W) (U : X.Opens)
    (hall : Stacks.Divisors.schemeAssociatedPoints X ⊆ (U : Set X)) :
    Function.Injective (((W.ι ⁻¹ᵁ U).ι).appTop).hom := by
  classical
  let S : Scheme := W.toScheme
  let V : S.Opens := W.ι ⁻¹ᵁ U
  let F : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let M : Type u := Γ(F, W)
  have hSaff : IsAffine S := hW
  have hFqc : F.IsQuasicoherent := inferInstance
  let : Module Γ(X, W) M := (F.val.obj (op W)).isModule
  have hnoeth : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  rw [RingHom.injective_iff_ker_eq_bot, RingHom.ker_eq_bot_iff_eq_zero]
  intro a hqa
  let aA : Γ(X, W) := W.topIso.hom a
  have hzero : assMap Γ(X, W) Γ(X, W) aA = 0 := by
    funext p
    let qspec : PrimeSpectrum Γ(X, W) := ⟨p.1, p.2.1⟩
    let z : S := hW.isoSpec.inv qspec
    let x : X := z.1
    have hxW : x ∈ W := z.2
    let y : W := z
    have hpEq : hW.primeIdealOf ⟨x, hxW⟩ = qspec := by
      change (hW.isoSpec.inv ≫ hW.isoSpec.hom) qspec = qspec
      rw [hW.isoSpec.inv_hom_id]
      rfl
    have hpStacks0 : (⊥ : Submodule Γ(X, W) Γ(X, W)).IsAssociatedPrime p.1 :=
      AssociatedPrimes.mem_iff.mp p.2
    obtain ⟨hp, m, hm⟩ := (Submodule.isAssociatedPrime_iff).mp hpStacks0
    let mM : M := cast (unit_sections_carrier_eq W).symm m
    have hpStacks : IsAssociatedPrimeStacks Γ(X, W) M p.1 := by
      refine ⟨hp, mM, ?_⟩
      ext r
      rw [hm, Submodule.mem_colon_span_singleton, Submodule.mem_colon_singleton]
      exact Iff.rfl
    have hpoint : x ∈ Stacks.Divisors.schemeAssociatedPoints X :=
      isAssociatedPoint_of_isAssociatedPrime_sections F W hW hxW (by simpa [hpEq] using hpStacks)
    have hzgerm : (W.toScheme.presheaf.germ ⊤ z (by simp)).hom a = 0 :=
      germ_eq_zero_of_open_restriction_eq_zero V z (hall hpoint) a hqa
    let : Algebra Γ(X, W) (X.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxW⟩
    let : IsLocalization.AtPrime (X.presheaf.stalk x) p.1 := by
      simpa [hpEq] using hW.isLocalization_stalk ⟨x, hxW⟩
    obtain ⟨s, hs⟩ :=
      (IsLocalization.map_eq_zero_iff p.1.primeCompl (X.presheaf.stalk x) aA).mp
        (by
          have hGerm : S.presheaf.germ ⊤ z (by simp) ≫ (W.stalkIso y).hom =
              X.presheaf.germ (W.ι ''ᵁ ⊤) x ⟨y, by trivial, rfl⟩ :=
            Scheme.Opens.germ_stalkIso_hom (X := X) (U := W) (V := ⊤) y (by trivial)
          have hGermApp := congrArg (fun k => k.hom a) hGerm
          have htransport := congrArg (fun t => (W.stalkIso y).hom t) hzgerm
          have htransport' :
              (S.presheaf.germ ⊤ z (by simp) ≫ (W.stalkIso y).hom).hom a = 0 := by
            change (W.stalkIso y).hom.hom ((S.presheaf.germ ⊤ z (by simp)).hom a) = 0
            simpa [S] using htransport
          rw [hGermApp] at htransport'
          have htopIsoGerm : X.presheaf.germ W x hxW (W.topIso.hom a) =
              X.presheaf.germ (W.ι ''ᵁ ⊤) x ⟨y, by trivial, rfl⟩ a := by
            rw [Scheme.Opens.topIso_hom]
            exact X.presheaf.germ_res_apply (i := eqToHom W.ι_image_top.symm) x hxW a
          change (X.presheaf.germ W x hxW).hom (W.topIso.hom a) = 0
          rw [htopIsoGerm]
          exact htransport')
    change LocalizedModule.mk aA 1 = 0
    rw [← LocalizedModule.zero_mk (S := p.1.primeCompl) 1, LocalizedModule.mk_eq]
    exact ⟨s, by simpa [Submonoid.smul_def, mul_comm, smul_eq_mul] using hs⟩
  have haA : aA = 0 := (zero_at_ass_zero Γ(X, W) Γ(X, W)) (by simpa using hzero)
  have hinj : Function.Injective W.topIso.hom :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance |>.1
  exact hinj (by simpa [aA] using haA)

/-- A dense open of a locally Noetherian scheme contains the generic point of every irreducible
component. -/
private lemma genericPoint_mem_of_dense_open {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U : X.Opens} (hU : Dense (U : Set X)) {Z : Set X} (hZ : Z ∈ irreducibleComponents X)
    {x : X} (hx : IsGenericPoint x Z) : x ∈ U := by
  by_contra hxU
  have hZoutside : Z ⊆ (U : Set X)ᶜ := fun y hyZ hyU =>
    hxU ((hx.specializes hyZ).mem_open U.2 hyU)
  obtain ⟨W, hWaff, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
  let Y : Scheme := W
  let C : Set Y := W.ι.base ⁻¹' Z
  have hrange : (Z ∩ Set.range W.ι.base).Nonempty := ⟨x, hx.mem, ⟨⟨x, hxW⟩, rfl⟩⟩
  have hC : C ∈ irreducibleComponents Y :=
    preimage_mem_irreducibleComponents hZ W.ι.isOpenEmbedding hrange
  have hnoeth : IsNoetherianRing Γ(X, W) := IsLocallyNoetherian.component_noetherian ⟨W, hWaff⟩
  have hns : TopologicalSpace.NoetherianSpace Y := noetherianSpace_of_isAffineOpen W hWaff
  obtain ⟨O, hOopen, hOne, hOC⟩ :=
    TopologicalSpace.NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent C hC
  let OX : Set X := W.ι.base '' O
  have hOXopen : IsOpen OX := W.ι.isOpenEmbedding.isOpenMap O hOopen
  have hOXne : OX.Nonempty := hOne.image _
  obtain ⟨_, ⟨y', hy'O, rfl⟩, hyU⟩ := hU.inter_open_nonempty OX hOXopen hOXne
  exact hZoutside (hOC hy'O) hyU

/-- An open containing the generic point of every irreducible component is dense. -/
private lemma dense_of_genericPoints_mem {X : Scheme.{u}} [IsLocallyNoetherian X]
    {U : X.Opens}
    (hU : ∀ C : irreducibleComponents X, (genericPoints.ofComponent C : X) ∈ U) :
    Dense (U : Set X) := by
  refine dense_iff_inter_open.mpr fun V hVopen ⟨x, hxV⟩ => ?_
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  exact ⟨_, ((genericPoints.isGenericPoint_ofComponent C).specializes
    mem_irreducibleComponent).mem_open hVopen hxV, hU C⟩

/-- **Stacks Project, Tag 083P.** For an open subscheme of a locally Noetherian scheme,
scheme-theoretic density is equivalent to topological density together with containment of every
embedded point, and also to containment of every associated point. -/
@[stacks 083P]
theorem isSchemeTheoreticallyDense_tfae (X : Scheme.{u}) [IsLocallyNoetherian X] (U : X.Opens) :
    List.TFAE [
      Scheme.Opens.IsSchemeTheoreticallyDense U,
      Dense (U : Set X) ∧ (∀ x : X, IsEmbeddedPoint X x → x ∈ U),
      Stacks.Divisors.schemeAssociatedPoints X ⊆ (U : Set X)] := by
  classical
  tfae_have 2 ↔ 3 := by
    constructor
    · rintro ⟨hdense, hemb⟩ x hx
      by_cases hgen : ∃ Z ∈ irreducibleComponents X, IsGenericPoint x Z
      · obtain ⟨Z, hZ, hgen⟩ := hgen
        exact genericPoint_mem_of_dense_open hdense hZ hgen
      · exact hemb x ((isEmbeddedPoint_iff_not_genericPoint X x).2 ⟨hx, hgen⟩)
    · exact fun hall => ⟨dense_of_genericPoints_mem fun C =>
        hall (mem_schemeAssociatedPoints_of_isGenericPoint_irreducibleComponent X C.2
          (genericPoints.isGenericPoint_ofComponent C)), fun x hx => hall hx.1⟩
  tfae_have 1 ↔ 3 := by
    constructor
    · intro h x hx
      by_contra hxU
      obtain ⟨W, hW, hxW, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) (by simp)
      let S : Scheme := W.toScheme
      let V : S.Opens := W.ι ⁻¹ᵁ U
      let q : V.toScheme ⟶ S := V.ι
      let F : X.Modules := SheafOfModules.unit X.ringCatSheaf
      let M : Type u := Γ(F, W)
      let A := Γ(X, W)
      let xW : W := ⟨x, hxW⟩
      have hSaff : IsAffine S := hW
      have hFqc : F.IsQuasicoherent := inferInstance
      let : Module A M := (F.val.obj (op W)).isModule
      have hxAssoc : Stacks.Divisors.IsAssociatedPoint F x := by
        simpa [Stacks.Divisors.mem_schemeAssociatedPoints_iff] using hx
      have hpStacks : IsAssociatedPrimeStacks A M (hW.primeIdealOf xW).asIdeal :=
        (isAssociatedPrime_sections_iff_isAssociatedPoint_of_isLocallyNoetherian
          F W hW hxW).2 hxAssoc
      obtain ⟨hp, m, hm⟩ := hpStacks
      let mA : A := cast (unit_sections_carrier_eq W).symm m
      have hm_ne : m ≠ 0 := by
        intro hm0
        refine hp.ne_top ?_
        rw [← hm, hm0]
        simp
      have hkill (r : A) (hr : r ∈ (hW.primeIdealOf xW).asIdeal) : r * mA = 0 := by
        have hr' : r ∈ (⊥ : Submodule A M).colon (Submodule.span A {m}) := hm.symm ▸ hr
        exact (by simpa using hr' : r • m = 0)
      let a : Γ(S, ⊤) := W.topIso.inv.hom mA
      have hqinj : Function.Injective q.appTop.hom :=
        (isSchemeTheoreticallyDominant_iff_appTop_injective_of_isAffine q).mp (h W)
      have hqzero : q.appTop.hom a = 0 := by
        apply V.toScheme.IsSheaf.section_ext
        intro y hy
        let z : S := q y
        let zW : W := ⟨z.1, z.2⟩
        let p := hW.primeIdealOf xW
        let qy := hW.primeIdealOf zW
        have hnot : ¬ p.asIdeal ≤ qy.asIdeal := by
          intro hpq
          have hspec : p ⤳ qy := (PrimeSpectrum.le_iff_specializes p qy).mp
            ((PrimeSpectrum.asIdeal_le_asIdeal p qy).mp hpq)
          have hid (w : S) : hW.isoSpec.inv (hW.isoSpec.hom w) = w := by
            change (hW.isoSpec.hom ≫ hW.isoSpec.inv).base w = w
            rw [hW.isoSpec.hom_inv_id]
            rfl
          have hspec' : (xW : S) ⤳ (z : S) := by
            have hmapped := hspec.map hW.isoSpec.inv.continuous
            change hW.isoSpec.inv (hW.isoSpec.hom xW) ⤳
              hW.isoSpec.inv (hW.isoSpec.hom z) at hmapped
            rwa [hid z, hid xW] at hmapped
          have hxV : (xW : S) ∈ V :=
            (specializes_iff_forall_open.mp hspec') (V : Set S) V.2 y.2
          have hxU' : x ∈ U := by
            change (W.ι xW) ∈ U at hxV
            simpa [xW] using hxV
          exact hxU hxU'
        obtain ⟨r, hrp, hrq⟩ := Set.not_subset.mp hnot
        let : qy.asIdeal.IsPrime := qy.isPrime
        let : Algebra A (X.presheaf.stalk z.1) := X.presheaf.algebra_section_stalk zW
        let : IsLocalization.AtPrime (X.presheaf.stalk z.1) qy.asIdeal := by
          simpa [qy] using hW.isLocalization_stalk zW
        have hrq' : r ∈ qy.asIdeal.primeCompl := hrq
        have hrun : IsUnit (algebraMap A (X.presheaf.stalk z.1) r) :=
          IsLocalization.map_units (S := X.presheaf.stalk z.1)
            (M := qy.asIdeal.primeCompl) ⟨r, hrq'⟩
        let aA : A := W.topIso.hom.hom a
        have hzeroA : algebraMap A (X.presheaf.stalk z.1) aA = 0 := by
          apply hrun.mul_left_cancel
          rw [← map_mul, show r * aA = 0 by simpa [aA, a] using hkill r hrp, map_zero, mul_zero]
        have htopIsoGerm : X.presheaf.germ W z.1 z.2 (W.topIso.hom a) =
            X.presheaf.germ (W.ι ''ᵁ ⊤) z.1 ⟨z, by trivial, rfl⟩ a := by
          rw [Scheme.Opens.topIso_hom]
          exact X.presheaf.germ_res_apply (i := eqToHom W.ι_image_top.symm) z.1 z.2 a
        have hzeroImage :
            (X.presheaf.germ (W.ι ''ᵁ ⊤) z.1 ⟨z, by trivial, rfl⟩).hom a = 0 := by
          rw [← htopIsoGerm]
          have hzeroW : (X.presheaf.germ W zW.1 zW.2).hom (W.topIso.hom a) = 0 := by
            rw [← X.presheaf.stalk_open_algebraMap zW]
            exact hzeroA
          simpa [zW] using hzeroW
        have hGerm : S.presheaf.germ ⊤ z (by simp) ≫ (W.stalkIso z).hom =
            X.presheaf.germ (W.ι ''ᵁ ⊤) z.1 ⟨z, by trivial, rfl⟩ :=
          Scheme.Opens.germ_stalkIso_hom (X := X) (U := W) (V := ⊤) z (by trivial)
        have hzeroSource : (S.presheaf.germ ⊤ z (by simp)).hom a = 0 := by
          have hzeroComp :
              (W.stalkIso z).hom.hom ((S.presheaf.germ ⊤ z (by simp)).hom a) = 0 := by
            rw [← ConcreteCategory.comp_apply, hGerm]
            exact hzeroImage
          have hinj : Function.Injective (W.stalkIso z).hom.hom :=
            (ConcreteCategory.isIso_iff_bijective _).mp inferInstance |>.1
          exact hinj (by simpa using hzeroComp)
        have hzeroTarget :
            (V.toScheme.presheaf.germ ⊤ y hy).hom (q.appTop.hom a) = 0 := by
          change (V.toScheme.presheaf.germ (q ⁻¹ᵁ ⊤) y (by simp)).hom ((q.app ⊤).hom a) = 0
          rw [← Scheme.Hom.germ_stalkMap_apply q ⊤ y (by simp) a]
          change (q.stalkMap y).hom ((S.presheaf.germ ⊤ z (by simp)).hom a) = 0
          rw [hzeroSource, map_zero]
        have hzeroTarget' : (V.toScheme.presheaf.germ ⊤ y hy).hom (q.appTop.hom a) =
            (V.toScheme.presheaf.germ ⊤ y (by trivial)).hom 0 := by
          rw [hzeroTarget, map_zero]
        obtain ⟨T, hyT, iTtop, iTtop', hT⟩ :=
          V.toScheme.presheaf.germ_eq (U := ⊤) (V := ⊤) y hy (by trivial)
            (q.appTop.hom a) 0 hzeroTarget'
        refine ⟨T, le_top, hyT, ?_⟩
        have hiTtop : iTtop = homOfLE (le_top : T ≤ ⊤) := Subsingleton.elim _ _
        have hiTtop' : iTtop' = homOfLE (le_top : T ≤ ⊤) := Subsingleton.elim _ _
        rw [hiTtop, hiTtop'] at hT
        simpa only [Scheme.Opens.toScheme_presheaf_map] using hT
      have ham : a ≠ 0 := by
        intro ha
        have hinj : Function.Injective W.topIso.inv.hom :=
          (ConcreteCategory.isIso_iff_bijective _).mp inferInstance |>.1
        have hma0 : mA = 0 := hinj (by
          change W.topIso.inv.hom mA = W.topIso.inv.hom 0
          simpa [a] using ha)
        have heq : (cast (unit_sections_carrier_eq W).symm m : A) = 0 := by
          simpa [mA] using hma0
        exact hm_ne ((Equiv.cast (unit_sections_carrier_eq W).symm).injective heq)
      exact ham (hqinj (by simpa using hqzero))
    · intro hall
      have hmono : Mono U.ι.c := (mono_c_iff_app_injective U.ι).2 fun V =>
        app_injective_of_app_injective_affine U.ι (fun W => by
          rw [app_injective_iff_appTop_inter]
          exact appTop_injective_of_associatedPoints_subset (W : X.Opens) W.2 U hall) V
      simpa [Scheme.Opens.opensRange_ι] using
        (isSchemeTheoreticallyDense_opensRange_iff_mono U.ι).2 hmono
  tfae_finish

end AlgebraicGeometry

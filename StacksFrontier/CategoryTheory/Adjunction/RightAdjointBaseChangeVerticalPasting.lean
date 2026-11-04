module

public import StacksFrontier.CategoryTheory.Adjunction.CounitCompatibleCoherence
public import StacksFrontier.CategoryTheory.Adjunction.RightAdjointBaseChangePasting

/-!
# Vertical pasting of base change maps of right adjoints

Consider two squares stacked vertically,

```
      Lk
  U ----→ U'
  ↑ Lh    ↑ Lh'
  T ----→ T'
  ↑ Lf    ↑ Lf'
  S ----→ S'
      Lg
```

with the middle row `Lg' : T ⥤ T'`, every vertical functor `Lf, Lh, Lf', Lh'` having a right
adjoint `Rf, Rh, Rf', Rh'` which in turn has a right adjoint `a, b, a', b'`, and an outer square
with vertical functors `Lo, Lo'` (right adjoints `Ro, Ro'`, right adjoints of those `c, c'`)
identified with the composites by `cL : Lf ⋙ Lh ≅ Lo` and `cL' : Lf' ⋙ Lh' ≅ Lo'`. The
induced identifications `cR : Rh ⋙ Rf ≅ Ro` and `cA : a ⋙ b ≅ c` are recorded through their
compatibility with the counits. If the comparison of the composite pullbacks around the outer
square is the pasting of the two inner ones, then the base change map of pushforward along
pullback of the outer square is the vertical pasting of the two inner ones, and so is the base
change map `c ⋙ Lk ⟶ Lg ⋙ c'` of the right adjoints.

This is the abstract form of the compatibility of the maps of [Stacks, Tag 0A9L] with the
composition of the proper morphisms, used in the proofs of [Stacks, Tag 0ATX] and
[Stacks, Tag 0ATY].

## Main results

* `Stacks.CategoryTheory.BaseChange.map_eq_of_pullbackComparison_vpaste` — vertical pasting of
  the base change maps of pushforward along pullback.
* `Stacks.CategoryTheory.BaseChange.rightAdjointBaseChange_app_eq_of_vpaste` — vertical pasting
  of the base change maps of the right adjoints.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

open Stacks.AffineProjectionFormula

variable {S T U S' T' U' : Type*} [Category S] [Category T] [Category U] [Category S']
  [Category T'] [Category U']
  {Lf : S ⥤ T} {Rf : T ⥤ S} {Lh : T ⥤ U} {Rh : U ⥤ T} {Lo : S ⥤ U} {Ro : U ⥤ S}
  {Lf' : S' ⥤ T'} {Rf' : T' ⥤ S'} {Lh' : T' ⥤ U'} {Rh' : U' ⥤ T'} {Lo' : S' ⥤ U'}
  {Ro' : U' ⥤ S'}
  (adjf : Lf ⊣ Rf) (adjh : Lh ⊣ Rh) (adjo : Lo ⊣ Ro) (adjf' : Lf' ⊣ Rf') (adjh' : Lh' ⊣ Rh')
  (adjo' : Lo' ⊣ Ro')
  {Lg : S ⥤ S'} {Lg' : T ⥤ T'} {Lk : U ⥤ U'} {Lc : S ⥤ T'} {Ld : T ⥤ U'} {Lco : S ⥤ U'}
  (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc) (eh : Lg' ⋙ Lh' ≅ Ld) (ek : Lh ⋙ Lk ≅ Ld)
  (ego : Lg ⋙ Lo' ≅ Lco) (efo : Lo ⋙ Lk ≅ Lco)
  (cL : Lf ⋙ Lh ≅ Lo) (cL' : Lf' ⋙ Lh' ≅ Lo') (cR : Rh ⋙ Rf ≅ Ro) (cR' : Rh' ⋙ Rf' ≅ Ro')

/-- The comparison of the composite pullbacks around the outer square is the vertical pasting of
the two inner comparisons, conjugated by `cL` and `cL'`. -/
def PullbackComparisonVPaste : Prop :=
  ∀ K : S, (ego.hom ≫ efo.inv).app K =
    cL'.inv.app (Lg.obj K) ≫ Lh'.map ((eg.hom ≫ ef.inv).app K) ≫
      (eh.hom ≫ ek.inv).app (Lf.obj K) ≫ Lk.map (cL.hom.app K)

/-- The counit compatibility of `cR`, with the composite counit unfolded. -/
private theorem counitCompatible_app (hR : CounitCompatible adjf adjh adjo cL cR) (M : U) :
    Lo.map (cR.hom.app M) ≫ adjo.counit.app M = cL.inv.app (Rf.obj (Rh.obj M)) ≫
      Lh.map (adjf.counit.app (Rh.obj M)) ≫ adjh.counit.app M := by
  simpa only [Adjunction.comp_counit_app, Functor.comp_obj] using hR M

/-- The counit of `adjo`, expressed through those of `adjf` and `adjh` by `cL` and `cR`. -/
theorem counit_app_eq_of_counitCompatible (hR : CounitCompatible adjf adjh adjo cL cR) (M : U) :
    adjo.counit.app M = Lo.map (cR.inv.app M) ≫ cL.inv.app (Rf.obj (Rh.obj M)) ≫
      Lh.map (adjf.counit.app (Rh.obj M)) ≫ adjh.counit.app M := by
  rw [← cancel_epi (Lo.map (cR.hom.app M)), counitCompatible_app adjf adjh adjo cL cR hR M,
    ← Lo.map_comp_assoc, Iso.hom_inv_id_app, Lo.map_id, Category.id_comp]

/-- The base change map followed by the counit of `adjf'` is the comparison of the composites
followed by `Lg'` of the counit of `adjf`. -/
private theorem map_comp_counit (N : T) :
    Lf'.map (map adjf adjf' eg ef N) ≫ adjf'.counit.app (Lg'.obj N) =
      eg.hom.app (Rf.obj N) ≫ ef.inv.app (Rf.obj N) ≫ Lg'.map (adjf.counit.app N) := by
  simpa only [Adjunction.homEquiv_counit] using homEquiv_symm_map adjf adjf' eg ef N

/-- The adjunct under `Lf' ⊣ Rf'` of `Lg f` followed by the base change map and `Rf' g`. -/
theorem map_map_comp_map_comp_counit {X : S} {N : T} {Y : T'} (f : X ⟶ Rf.obj N)
    (g : Lg'.obj N ⟶ Y) :
    Lf'.map (Lg.map f ≫ map adjf adjf' eg ef N ≫ Rf'.map g) ≫ adjf'.counit.app Y =
      (eg.hom ≫ ef.inv).app X ≫ Lg'.map (Lf.map f) ≫ Lg'.map (adjf.counit.app N) ≫ g := by
  have h₁ := map_comp_counit adjf adjf' eg ef N
  have n₂ := adjf'.counit.naturality g
  simp only [Functor.comp_map, Functor.id_map] at n₂
  have n₄ := (eg.hom ≫ ef.inv).naturality f
  simp only [Functor.comp_map, NatTrans.comp_app, Category.assoc] at n₄
  simp only [Functor.map_comp, Category.assoc, NatTrans.comp_app]
  rw [n₂, reassoc_of% h₁, reassoc_of% n₄]

/-- **Vertical pasting of the base change maps of pushforward along pullback.** -/
theorem map_eq_of_pullbackComparison_vpaste
    (hpc : PullbackComparisonVPaste eg ef eh ek ego efo cL cL')
    (hR : CounitCompatible adjf adjh adjo cL cR) (hR' : CounitCompatible adjf' adjh' adjo' cL' cR')
    (M : U) :
    map adjo adjo' ego efo M =
      Lg.map (cR.inv.app M) ≫ map adjf adjf' eg ef (Rh.obj M) ≫
        Rf'.map (map adjh adjh' eh ek M) ≫ cR'.hom.app (Lk.obj M) := by
  apply (adjo'.homEquiv _ _).symm.injective
  rw [homEquiv_symm_map, Adjunction.homEquiv_counit]
  have h₂ := map_comp_counit adjh adjh' eh ek M
  have hR'M := counitCompatible_app adjf' adjh' adjo' cL' cR' hR' (Lk.obj M)
  have hp := hpc (Ro.obj M)
  simp only [NatTrans.comp_app] at hp
  -- the adjunct of `Lh(Lf cR⁻¹) ≫ Lh(ε_f) ≫ ε_h` is `Lk` of `cL ≫ ε_o`
  have k₂ : cL.hom.app (Ro.obj M) ≫ adjo.counit.app M =
      Lh.map (Lf.map (cR.inv.app M) ≫ adjf.counit.app (Rh.obj M)) ≫ adjh.counit.app M := by
    rw [counit_app_eq_of_counitCompatible adjf adjh adjo cL cR hR M, ← cL.hom.naturality_assoc]
    simp
  have n₃ := (eh.hom ≫ ek.inv).naturality
    (Lf.map (cR.inv.app M) ≫ adjf.counit.app (Rh.obj M))
  simp only [Functor.comp_map] at n₃
  calc ego.hom.app (Ro.obj M) ≫ efo.inv.app (Ro.obj M) ≫ Lk.map (adjo.counit.app M)
      = cL'.inv.app (Lg.obj (Ro.obj M)) ≫ Lh'.map ((eg.hom ≫ ef.inv).app (Ro.obj M)) ≫
          (eh.hom ≫ ek.inv).app (Lf.obj (Ro.obj M)) ≫
            Lk.map (cL.hom.app (Ro.obj M) ≫ adjo.counit.app M) := by
        rw [← Category.assoc, hp]
        simp
    _ = cL'.inv.app (Lg.obj (Ro.obj M)) ≫ Lh'.map ((eg.hom ≫ ef.inv).app (Ro.obj M)) ≫
          Lh'.map (Lg'.map (Lf.map (cR.inv.app M) ≫ adjf.counit.app (Rh.obj M))) ≫
            (eh.hom ≫ ek.inv).app (Rh.obj M) ≫ Lk.map (adjh.counit.app M) := by
        rw [k₂, Lk.map_comp, ← reassoc_of% n₃]
    _ = cL'.inv.app (Lg.obj (Ro.obj M)) ≫
          Lh'.map (Lf'.map (Lg.map (cR.inv.app M) ≫ map adjf adjf' eg ef (Rh.obj M) ≫
            Rf'.map (map adjh adjh' eh ek M)) ≫ adjf'.counit.app _) ≫
            adjh'.counit.app (Lk.obj M) := by
        rw [map_map_comp_map_comp_counit adjf adjf' eg ef (cR.inv.app M)
          (map adjh adjh' eh ek M)]
        simp [h₂]
    _ = _ := by
        simp only [Functor.map_comp, Category.assoc]
        rw [hR'M]
        simp only [NatTrans.naturality_assoc, Functor.comp_map]

/-- **Vertical pasting of the inverse base change maps of pushforward along pullback.** -/
theorem inv_twoSquare_app_eq_of_vpaste
    (hpc : PullbackComparisonVPaste eg ef eh ek ego efo cL cL')
    (hR : CounitCompatible adjf adjh adjo cL cR) (hR' : CounitCompatible adjf' adjh' adjo' cL' cR')
    [IsIso (twoSquare adjf adjf' eg ef).natTrans] [IsIso (twoSquare adjh adjh' eh ek).natTrans]
    [IsIso (twoSquare adjo adjo' ego efo).natTrans] (M : U) :
    (inv (twoSquare adjo adjo' ego efo).natTrans).app M =
      cR'.inv.app (Lk.obj M) ≫ Rf'.map ((inv (twoSquare adjh adjh' eh ek).natTrans).app M) ≫
        (inv (twoSquare adjf adjf' eg ef).natTrans).app (Rh.obj M) ≫ Lg.map (cR.hom.app M) := by
  simp only [NatIso.isIso_inv_app]
  apply IsIso.inv_eq_of_hom_inv_id
  change map adjo adjo' ego efo M ≫ _ = _
  rw [map_eq_of_pullbackComparison_vpaste adjf adjh adjo adjf' adjh' adjo' eg ef eh ek ego efo cL
    cL' cR cR' hpc hR hR' M]
  simp [map, ← Lg.map_comp]

section RightAdjoint

variable {a : S ⥤ T} {b : T ⥤ U} {c : S ⥤ U} {a' : S' ⥤ T'} {b' : T' ⥤ U'} {c' : S' ⥤ U'}
  (adja : Rf ⊣ a) (adjb : Rh ⊣ b) (adjc : Ro ⊣ c) (adja' : Rf' ⊣ a') (adjb' : Rh' ⊣ b')
  (adjc' : Ro' ⊣ c') (cA : a ⋙ b ≅ c) (cA' : a' ⋙ b' ≅ c')
  {Rg : S' ⥤ S} {Rg' : T' ⥤ T} {Rk : U' ⥤ U} (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg')
  (adjk : Lk ⊣ Rk)

variable [IsIso (twoSquare adjf adjf' eg ef).natTrans] [IsIso (twoSquare adjh adjh' eh ek).natTrans]
  [IsIso (twoSquare adjo adjo' ego efo).natTrans]

/-- The inverse base change map of the outer square followed by the counit of `c` is the vertical
pasting of the inner inverse base change maps followed by the counits of `b` and `a`. -/
theorem inv_twoSquare_app_comp_map_counit_of_vpaste
    (hpc : PullbackComparisonVPaste eg ef eh ek ego efo cL cL')
    (hR : CounitCompatible adjf adjh adjo cL cR) (hR' : CounitCompatible adjf' adjh' adjo' cL' cR')
    (hA : CounitCompatible adjb adja adjc cR cA) (K : S) :
    (inv (twoSquare adjo adjo' ego efo).natTrans).app (c.obj K) ≫ Lg.map (adjc.counit.app K) =
      Ro'.map (Lk.map (cA.inv.app K)) ≫ cR'.inv.app (Lk.obj (b.obj (a.obj K))) ≫
        Rf'.map ((inv (twoSquare adjh adjh' eh ek).natTrans).app (b.obj (a.obj K))) ≫
        (inv (twoSquare adjf adjf' eg ef).natTrans).app (Rh.obj (b.obj (a.obj K))) ≫
        Lg.map (Rf.map (adjb.counit.app (a.obj K))) ≫ Lg.map (adja.counit.app K) := by
  have hv := inv_twoSquare_app_eq_of_vpaste adjf adjh adjo adjf' adjh' adjo' eg ef eh ek ego efo
    cL cL' cR cR' hpc hR hR' (b.obj (a.obj K))
  have nbc := (inv (twoSquare adjo adjo' ego efo).natTrans).naturality (cA.inv.app K)
  simp only [Functor.comp_map] at nbc
  rw [counit_app_eq_of_counitCompatible adjb adja adjc cR cA hA K]
  simp only [Functor.map_comp]
  rw [← reassoc_of% nbc, reassoc_of% hv, ← Lg.map_comp_assoc (cR.hom.app _) (cR.inv.app _),
    Iso.hom_inv_id_app, Lg.map_id, Category.id_comp]

/-- **Vertical pasting of the base change maps of the right adjoints.** If the comparison of the
composite pullbacks around the outer square is the vertical pasting of the two inner ones, the
base change map `c ⋙ Lk ⟶ Lg ⋙ c'` of the outer square at `K` is that of the upper square at
`a K` followed by `b'` of that of the lower square, conjugated by `cA` and `cA'`. -/
theorem rightAdjointBaseChange_app_eq_of_vpaste
    (hpc : PullbackComparisonVPaste eg ef eh ek ego efo cL cL')
    (hR : CounitCompatible adjf adjh adjo cL cR) (hR' : CounitCompatible adjf' adjh' adjo' cL' cR')
    (hA : CounitCompatible adjb adja adjc cR cA)
    (hA' : CounitCompatible adjb' adja' adjc' cR' cA') (K : S) :
    haveI := isIso_rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja'
    haveI := isIso_rightAdjointSquare adjh adjh' adjg' adjk eh ek adjb adjb'
    haveI := isIso_rightAdjointSquare adjo adjo' adjg adjk ego efo adjc adjc'
    (rightAdjointBaseChange adjo adjo' adjg adjk ego efo adjc adjc').natTrans.app K =
      Lk.map (cA.inv.app K) ≫
        (rightAdjointBaseChange adjh adjh' adjg' adjk eh ek adjb adjb').natTrans.app (a.obj K) ≫
        b'.map ((rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').natTrans.app K) ≫
        cA'.hom.app (Lg.obj K) := by
  have := isIso_rightAdjointSquare adjf adjf' adjg adjg' eg ef adja adja'
  have := isIso_rightAdjointSquare adjh adjh' adjg' adjk eh ek adjb adjb'
  have := isIso_rightAdjointSquare adjo adjo' adjg adjk ego efo adjc adjc'
  apply (adjc'.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
    map_rightAdjointBaseChange_comp_counit]
  set β₁ := (rightAdjointBaseChange adjf adjf' adjg adjg' eg ef adja adja').natTrans
  set β₂ := (rightAdjointBaseChange adjh adjh' adjg' adjk eh ek adjb adjb').natTrans
  have hβ₁ : Rf'.map (β₁.app K) ≫ adja'.counit.app (Lg.obj K) =
      (inv (twoSquare adjf adjf' eg ef).natTrans).app (a.obj K) ≫ Lg.map (adja.counit.app K) :=
    map_rightAdjointBaseChange_comp_counit adjf adjf' adjg adjg' eg ef adja adja' K
  have hβ₂ : Rh'.map (β₂.app (a.obj K)) ≫ adjb'.counit.app (Lg'.obj (a.obj K)) =
      (inv (twoSquare adjh adjh' eh ek).natTrans).app (b.obj (a.obj K)) ≫
        Lg'.map (adjb.counit.app (a.obj K)) :=
    map_rightAdjointBaseChange_comp_counit adjh adjh' adjg' adjk eh ek adjb adjb' (a.obj K)
  have hA'K := counitCompatible_app adjb' adja' adjc' cR' cA' hA' (Lg.obj K)
  have nbc₁ := (inv (twoSquare adjf adjf' eg ef).natTrans).naturality (adjb.counit.app (a.obj K))
  have nε := adjb'.counit.naturality (β₁.app K)
  have ncR := cR'.inv.naturality (β₂.app (a.obj K) ≫ b'.map (β₁.app K))
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj] at nbc₁ nε ncR
  calc (inv (twoSquare adjo adjo' ego efo).natTrans).app (c.obj K) ≫
        Lg.map (adjc.counit.app K)
      = Ro'.map (Lk.map (cA.inv.app K)) ≫ cR'.inv.app (Lk.obj (b.obj (a.obj K))) ≫
          Rf'.map ((inv (twoSquare adjh adjh' eh ek).natTrans).app (b.obj (a.obj K))) ≫
          (inv (twoSquare adjf adjf' eg ef).natTrans).app (Rh.obj (b.obj (a.obj K))) ≫
          Lg.map (Rf.map (adjb.counit.app (a.obj K))) ≫ Lg.map (adja.counit.app K) :=
        inv_twoSquare_app_comp_map_counit_of_vpaste adjf adjh adjo adjf' adjh' adjo' eg ef eh ek
          ego efo cL cL' cR cR' adja adjb adjc cA hpc hR hR' hA K
    _ = Ro'.map (Lk.map (cA.inv.app K)) ≫ cR'.inv.app (Lk.obj (b.obj (a.obj K))) ≫
          Rf'.map (Rh'.map (β₂.app (a.obj K)) ≫ adjb'.counit.app (Lg'.obj (a.obj K))) ≫
          Rf'.map (β₁.app K) ≫ adja'.counit.app (Lg.obj K) := by
        rw [hβ₁, hβ₂, Rf'.map_comp_assoc, reassoc_of% nbc₁]
    _ = _ := by
        rw [← Rf'.map_comp_assoc, Category.assoc, ← nε, ← Rh'.map_comp_assoc,
          Rf'.map_comp_assoc, ← reassoc_of% ncR]
        simp [hA'K]

end RightAdjoint

end Stacks.CategoryTheory.BaseChange

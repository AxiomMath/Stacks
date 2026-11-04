module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Equivalence

/-!
# Base change comparisons built from a unit and a counit, and their composition law

Let `asc ⊣ res` and `asc' ⊣ res'` be adjunctions, `P` and `p` functors between their sources
and targets, and `A : p ⋙ asc' ≅ asc ⋙ P` a comparison of the left adjoints.  On an object at
which the counit of `asc ⊣ res` and the unit of `asc' ⊣ res'` are invertible, the right adjoints
commute with base change as well:
`res' (P M) ≅ res' (P (asc (res M))) ≅ res' (asc' (p (res M))) ≅ p (res M)`.
This file names that comparison, reads it through equivalences of categories presenting the
right adjoints, and proves that it is compatible with composition as soon as the comparisons
`A` and the comparisons of the equivalences are.

Everything here is at variable categories; the point is that the concrete instances (modules on
the small étale site of a representable algebraic space, on the small étale site of a scheme and
on its Zariski site) are expensive to elaborate, and only a single instantiation of the
composition law below is needed there.

## Main definitions

* `Stacks.UnitCounitBaseChange.baseChangeOfUnit`: `res' (P (asc G)) ⟶ p G`, through the
  comparison `A` and the inverse of the unit of `asc' ⊣ res'`.
* `Stacks.UnitCounitBaseChange.baseChangeOfCounitUnit`: `res' (P M) ⟶ p (res M)`, through the
  inverse of the counit of `asc ⊣ res` and `baseChangeOfUnit`.
* `Stacks.UnitCounitBaseChange.baseChangeAlongEquivalence`: the same comparison when the right
  adjoints are read through equivalences `E`, `E'` and comparisons `ι`, `ι'`, written as the
  composite of six factors.

## Main results

* `Stacks.UnitCounitBaseChange.baseChangeAlongEquivalence_eq`: the six factors collapse to
  `ι'`, the comparison `R` of the equivalences, `baseChangeOfCounitUnit` and `ι⁻¹`.
* `Stacks.UnitCounitBaseChange.baseChangeOfCounitUnit_comp` and
  `Stacks.UnitCounitBaseChange.baseChangeAlongEquivalence_comp`: **the comparisons compose**,
  given that the comparisons `A` and `R` do.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.UnitCounitBaseChange

variable {X Y Z X' Y' Z' X'' Y'' Z'' : Type*} [Category X] [Category Y] [Category Z]
  [Category X'] [Category Y'] [Category Z'] [Category X''] [Category Y''] [Category Z'']

/-- A natural transformation invertible at one object is invertible at every isomorphic
object. -/
theorem isIso_app_of_iso {C D : Type*} [Category C] [Category D] {F G : C ⥤ D} (α : F ⟶ G)
    {c c' : C} (e : c ≅ c') [IsIso (α.app c)] : IsIso (α.app c') := by
  rw [show α.app c' = F.map e.inv ≫ α.app c ≫ G.map e.hom by
    rw [← α.naturality, ← Functor.map_comp_assoc, e.inv_hom_id, Functor.map_id,
      Category.id_comp]]
  infer_instance

/-- The inverse of an invertible component of the unit of an adjunction is natural. -/
theorem inv_unit_naturality {L : Z' ⥤ Y'} {R : Y' ⥤ Z'} (adj : L ⊣ R) {H H' : Z'} (f : H ⟶ H')
    [IsIso (adj.unit.app H)] [IsIso (adj.unit.app H')] :
    inv (adj.unit.app H) ≫ f = R.map (L.map f) ≫ inv (adj.unit.app H') := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv]
  exact adj.unit.naturality f

/-- The inverse of an invertible component of the counit of an adjunction is natural. -/
theorem inv_counit_naturality {L : Z' ⥤ Y'} {R : Y' ⥤ Z'} (adj : L ⊣ R) {M M' : Y'}
    (f : M ⟶ M') [IsIso (adj.counit.app M)] [IsIso (adj.counit.app M')] :
    inv (adj.counit.app M) ≫ L.map (R.map f) = f ≫ inv (adj.counit.app M') := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, adj.counit_naturality]

/-- The comparison `res' (P (asc G)) ⟶ p G`: the comparison `A` of the left adjoints, followed
by the inverse of the unit of `asc' ⊣ res'`. -/
noncomputable def baseChangeOfUnit {asc : Z ⥤ Y} {res' : Y' ⥤ Z'} {asc' : Z' ⥤ Y'}
    (adj' : asc' ⊣ res') {P : Y ⥤ Y'} {p : Z ⥤ Z'} (A : p ⋙ asc' ≅ asc ⋙ P) (G : Z)
    [IsIso (adj'.unit.app (p.obj G))] :
    res'.obj (P.obj (asc.obj G)) ⟶ p.obj G :=
  res'.map ((A.app G).inv) ≫ inv (adj'.unit.app (p.obj G))

/-- `Stacks.UnitCounitBaseChange.baseChangeOfUnit` is natural. -/
theorem baseChangeOfUnit_naturality {asc : Z ⥤ Y} {res' : Y' ⥤ Z'} {asc' : Z' ⥤ Y'}
    (adj' : asc' ⊣ res') {P : Y ⥤ Y'} {p : Z ⥤ Z'} (A : p ⋙ asc' ≅ asc ⋙ P) {G G' : Z}
    (f : G ⟶ G') [IsIso (adj'.unit.app (p.obj G))] [IsIso (adj'.unit.app (p.obj G'))] :
    baseChangeOfUnit adj' A G ≫ p.map f =
      res'.map (P.map (asc.map f)) ≫ baseChangeOfUnit adj' A G' := by
  have h1 : (A.app G).inv ≫ asc'.map (p.map f) = P.map (asc.map f) ≫ (A.app G').inv :=
    (A.inv.naturality f).symm
  unfold baseChangeOfUnit
  rw [Category.assoc, inv_unit_naturality adj' (p.map f), ← Category.assoc,
    ← res'.map_comp, h1, res'.map_comp, Category.assoc]

/-- The comparison `res' (P M) ⟶ p (res M)` at an object at which the counit of `asc ⊣ res`
and the unit of `asc' ⊣ res'` are invertible: the inverse of the counit, the comparison `A` of
the left adjoints and the inverse of the unit. -/
noncomputable def baseChangeOfCounitUnit {res : Y ⥤ Z} {asc : Z ⥤ Y} (adj : asc ⊣ res)
    {res' : Y' ⥤ Z'} {asc' : Z' ⥤ Y'} (adj' : asc' ⊣ res') {P : Y ⥤ Y'} {p : Z ⥤ Z'}
    (A : p ⋙ asc' ≅ asc ⋙ P) (M : Y) [IsIso (adj.counit.app M)]
    [IsIso (adj'.unit.app (p.obj (res.obj M)))] :
    res'.obj (P.obj M) ⟶ p.obj (res.obj M) :=
  res'.map (P.map (inv (adj.counit.app M))) ≫ baseChangeOfUnit adj' A (res.obj M)

/-- `Stacks.UnitCounitBaseChange.baseChangeOfCounitUnit` is natural. -/
theorem baseChangeOfCounitUnit_naturality {res : Y ⥤ Z} {asc : Z ⥤ Y} (adj : asc ⊣ res)
    {res' : Y' ⥤ Z'} {asc' : Z' ⥤ Y'} (adj' : asc' ⊣ res') {P : Y ⥤ Y'} {p : Z ⥤ Z'}
    (A : p ⋙ asc' ≅ asc ⋙ P) {M M' : Y} (f : M ⟶ M') [IsIso (adj.counit.app M)]
    [IsIso (adj'.unit.app (p.obj (res.obj M)))] [IsIso (adj.counit.app M')]
    [IsIso (adj'.unit.app (p.obj (res.obj M')))] :
    baseChangeOfCounitUnit adj adj' A M ≫ p.map (res.map f) =
      res'.map (P.map f) ≫ baseChangeOfCounitUnit adj adj' A M' := by
  unfold baseChangeOfCounitUnit
  rw [Category.assoc, baseChangeOfUnit_naturality, ← Category.assoc, ← res'.map_comp,
    ← P.map_comp, inv_counit_naturality, P.map_comp, res'.map_comp, Category.assoc]

/-- **The comparisons `baseChangeOfUnit` compose**, given the composition law `hA` of the
comparisons of the left adjoints. -/
theorem baseChangeOfUnit_comp {asc₀ : Z ⥤ Y} {res₁ : Y' ⥤ Z'} {asc₁ : Z' ⥤ Y'}
    (adj₁ : asc₁ ⊣ res₁) {res₂ : Y'' ⥤ Z''} {asc₂ : Z'' ⥤ Y''} (adj₂ : asc₂ ⊣ res₂)
    {P₁ : Y ⥤ Y'} {P₂ : Y' ⥤ Y''} {P : Y ⥤ Y''} {p₁ : Z ⥤ Z'} {p₂ : Z' ⥤ Z''} {p : Z ⥤ Z''}
    (A₁ : p₁ ⋙ asc₁ ≅ asc₀ ⋙ P₁) (A₂ : p₂ ⋙ asc₂ ≅ asc₁ ⋙ P₂) (A : p ⋙ asc₂ ≅ asc₀ ⋙ P)
    (cY : P₁ ⋙ P₂ ≅ P) (cZ : p₁ ⋙ p₂ ≅ p)
    (hA : Functor.isoWhiskerLeft p₁ A₂ ≪≫ Functor.isoWhiskerRight A₁ P₂ ≪≫
        Functor.isoWhiskerLeft asc₀ cY = Functor.isoWhiskerRight cZ asc₂ ≪≫ A)
    (G : Z) [IsIso (adj₂.unit.app (p.obj G))]
    [IsIso (adj₂.unit.app (p₂.obj (res₁.obj (P₁.obj (asc₀.obj G)))))]
    [IsIso (adj₁.unit.app (p₁.obj G))] [IsIso (adj₁.counit.app (P₁.obj (asc₀.obj G)))] :
    baseChangeOfUnit adj₂ A G ≫ cZ.inv.app G =
      res₂.map (cY.inv.app (asc₀.obj G)) ≫
        res₂.map (P₂.map (inv (adj₁.counit.app (P₁.obj (asc₀.obj G))))) ≫
        baseChangeOfUnit adj₂ A₂ (res₁.obj (P₁.obj (asc₀.obj G))) ≫
        p₂.map (baseChangeOfUnit adj₁ A₁ G) := by
  have : IsIso (adj₂.unit.app (p₂.obj (p₁.obj G))) :=
    isIso_app_of_iso (c := p.obj G) (c' := p₂.obj (p₁.obj G)) adj₂.unit (cZ.app G).symm
  have : IsIso (adj₂.unit.app (p₂.obj (res₁.obj (asc₁.obj (p₁.obj G))))) :=
    isIso_app_of_iso (c := p₂.obj (res₁.obj (P₁.obj (asc₀.obj G))))
      (c' := p₂.obj (res₁.obj (asc₁.obj (p₁.obj G)))) adj₂.unit
      (p₂.mapIso (res₁.mapIso (A₁.app G))).symm
  have htri' : asc₁.map (adj₁.unit.app (p₁.obj G)) ≫ adj₁.counit.app (asc₁.obj (p₁.obj G)) =
      𝟙 _ := adj₁.left_triangle_components _
  have : IsIso (asc₁.map (adj₁.unit.app (p₁.obj G)) ≫ adj₁.counit.app (asc₁.obj (p₁.obj G))) := by
    rw [htri']; infer_instance
  have : IsIso (adj₁.counit.app (asc₁.obj (p₁.obj G))) :=
    IsIso.of_isIso_comp_left (asc₁.map (adj₁.unit.app (p₁.obj G))) _
  have htri : inv (adj₁.counit.app (asc₁.obj (p₁.obj G))) =
      asc₁.map (adj₁.unit.app (p₁.obj G)) :=
    IsIso.inv_eq_of_inv_hom_id htri'
  have hAG : (A.app G).inv ≫ asc₂.map (cZ.inv.app G) =
      cY.inv.app (asc₀.obj G) ≫ P₂.map ((A₁.app G).inv) ≫ (A₂.app (p₁.obj G)).inv := by
    have h := congrArg (fun e => e.inv.app G) hA
    simp only [Iso.trans_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_inv,
      Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Category.assoc] at h
    simpa only [Iso.app_inv] using h.symm
  have n1 := baseChangeOfUnit_naturality adj₂ A₂ (G := res₁.obj (P₁.obj (asc₀.obj G)))
    (G' := res₁.obj (asc₁.obj (p₁.obj G))) (res₁.map ((A₁.app G).inv))
  have n2 := inv_counit_naturality adj₁ (M := P₁.obj (asc₀.obj G))
    (M' := asc₁.obj (p₁.obj G)) ((A₁.app G).inv)
  have n3 := baseChangeOfUnit_naturality adj₂ A₂ (G := p₁.obj G)
    (G' := res₁.obj (asc₁.obj (p₁.obj G))) (adj₁.unit.app (p₁.obj G))
  have n4 := inv_unit_naturality adj₂ (H := p.obj G) (H' := p₂.obj (p₁.obj G)) (cZ.inv.app G)
  have hu : p₂.map (adj₁.unit.app (p₁.obj G)) ≫ p₂.map (inv (adj₁.unit.app (p₁.obj G))) = 𝟙 _ := by
    simp
  have n2' : res₂.map (P₂.map (inv (adj₁.counit.app (P₁.obj (asc₀.obj G))))) ≫
      res₂.map (P₂.map (asc₁.map (res₁.map ((A₁.app G).inv)))) =
      res₂.map (P₂.map ((A₁.app G).inv)) ≫
        res₂.map (P₂.map (asc₁.map (adj₁.unit.app (p₁.obj G)))) := by
    rw [← res₂.map_comp, ← P₂.map_comp, n2, htri, P₂.map_comp, res₂.map_comp]
  simp only [baseChangeOfUnit, Functor.map_comp, Category.assoc] at n1 n3 ⊢
  rw [reassoc_of% n1, reassoc_of% n2', ← reassoc_of% n3, hu]
  dsimp only [Functor.id_obj]
  rw [Category.comp_id, n4, ← res₂.map_comp_assoc, hAG]
  simp only [Functor.map_comp, Category.assoc]

/-- **The comparisons `baseChangeOfCounitUnit` compose**, given the composition law `hA` of
the comparisons of the left adjoints. -/
theorem baseChangeOfCounitUnit_comp {res₀ : Y ⥤ Z} {asc₀ : Z ⥤ Y} (adj₀ : asc₀ ⊣ res₀)
    {res₁ : Y' ⥤ Z'} {asc₁ : Z' ⥤ Y'} (adj₁ : asc₁ ⊣ res₁) {res₂ : Y'' ⥤ Z''} {asc₂ : Z'' ⥤ Y''}
    (adj₂ : asc₂ ⊣ res₂) {P₁ : Y ⥤ Y'} {P₂ : Y' ⥤ Y''} {P : Y ⥤ Y''} {p₁ : Z ⥤ Z'}
    {p₂ : Z' ⥤ Z''} {p : Z ⥤ Z''}
    (A₁ : p₁ ⋙ asc₁ ≅ asc₀ ⋙ P₁) (A₂ : p₂ ⋙ asc₂ ≅ asc₁ ⋙ P₂) (A : p ⋙ asc₂ ≅ asc₀ ⋙ P)
    (cY : P₁ ⋙ P₂ ≅ P) (cZ : p₁ ⋙ p₂ ≅ p)
    (hA : Functor.isoWhiskerLeft p₁ A₂ ≪≫ Functor.isoWhiskerRight A₁ P₂ ≪≫
        Functor.isoWhiskerLeft asc₀ cY = Functor.isoWhiskerRight cZ asc₂ ≪≫ A)
    (M : Y) [IsIso (adj₀.counit.app M)] [IsIso (adj₂.unit.app (p.obj (res₀.obj M)))]
    [IsIso (adj₁.unit.app (p₁.obj (res₀.obj M)))] [IsIso (adj₁.counit.app (P₁.obj M))]
    [IsIso (adj₂.unit.app (p₂.obj (res₁.obj (P₁.obj M))))] :
    baseChangeOfCounitUnit adj₀ adj₂ A M ≫ cZ.inv.app (res₀.obj M) =
      res₂.map (cY.inv.app M) ≫ baseChangeOfCounitUnit adj₁ adj₂ A₂ (P₁.obj M) ≫
        p₂.map (baseChangeOfCounitUnit adj₀ adj₁ A₁ M) := by
  have : IsIso (adj₁.counit.app (P₁.obj (asc₀.obj (res₀.obj M)))) :=
    isIso_app_of_iso (c := P₁.obj M) adj₁.counit (P₁.mapIso (asIso (adj₀.counit.app M)).symm)
  have : IsIso (adj₂.unit.app (p₂.obj (res₁.obj (P₁.obj (asc₀.obj (res₀.obj M)))))) :=
    isIso_app_of_iso (c := p₂.obj (res₁.obj (P₁.obj M))) adj₂.unit
      (p₂.mapIso (res₁.mapIso (P₁.mapIso (asIso (adj₀.counit.app M)).symm)))
  have h1 := baseChangeOfUnit_comp adj₁ adj₂ A₁ A₂ A cY cZ hA (res₀.obj M)
  have n1 := baseChangeOfUnit_naturality adj₂ A₂ (G := res₁.obj (P₁.obj M))
    (G' := res₁.obj (P₁.obj (asc₀.obj (res₀.obj M))))
    (res₁.map (P₁.map (inv (adj₀.counit.app M))))
  have n2 := inv_counit_naturality adj₁ (M := P₁.obj M)
    (M' := P₁.obj (asc₀.obj (res₀.obj M))) (P₁.map (inv (adj₀.counit.app M)))
  have n3 : P.map (inv (adj₀.counit.app M)) ≫ cY.inv.app (asc₀.obj (res₀.obj M)) =
      cY.inv.app M ≫ P₂.map (P₁.map (inv (adj₀.counit.app M))) :=
    cY.inv.naturality (inv (adj₀.counit.app M))
  unfold baseChangeOfCounitUnit
  simp only [Category.assoc, Functor.map_comp]
  rw [h1, reassoc_of% n1, ← res₂.map_comp_assoc (P₂.map (inv (adj₁.counit.app (P₁.obj M)))),
    ← P₂.map_comp, n2, P₂.map_comp, res₂.map_comp_assoc,
    ← res₂.map_comp_assoc (cY.inv.app M), ← n3, res₂.map_comp_assoc]

/-- **The comparison `ρ' (φ N) ⟶ p (ρ N)` of the right adjoints read through equivalences**, as the
composite of six factors: `E`, `E'` present `ρ`, `ρ'` as `res`, `res'` through `ι`, `ι'`, and `R`
compares the base changes `φ` and `P` across the equivalences.  The factors are the inverse of
the counit of `asc ⊣ res` carried by `φ`, the comparisons `R` and `A`, `ι'`, the unit of `E'` and
the inverse of the unit of `asc' ⊣ res'`, and `ι⁻¹`. -/
noncomputable def baseChangeAlongEquivalence (E : Y ≌ X) (E' : Y' ≌ X') {ρ : X ⥤ Z} {ρ' : X' ⥤ Z'}
    {res : Y ⥤ Z} {asc : Z ⥤ Y} (adj : asc ⊣ res) {res' : Y' ⥤ Z'}
    {asc' : Z' ⥤ Y'} (adj' : asc' ⊣ res') (ι : ∀ N, ρ.obj N ≅ res.obj (E.inverse.obj N))
    (ι' : ∀ N', ρ'.obj N' ≅ res'.obj (E'.inverse.obj N')) {φ : X ⥤ X'} {P : Y ⥤ Y'} {p : Z ⥤ Z'}
    (R : φ ⋙ E'.inverse ≅ E.inverse ⋙ P) (A : p ⋙ asc' ≅ asc ⋙ P) (N : X)
    [hc : IsIso (adj.counit.app (E.inverse.obj N))]
    [hu : IsIso (adj'.unit.app (p.obj (res.obj (E.inverse.obj N))))] :
    ρ'.obj (φ.obj N) ≅ p.obj (ρ.obj N) :=
  ρ'.mapIso (φ.mapIso ((E.counitIso.app N).symm ≪≫
      E.functor.mapIso (asIso (adj.counit.app (E.inverse.obj N))).symm)) ≪≫
    ρ'.mapIso
      ((E'.counitIso.app (φ.obj (E.functor.obj (asc.obj (res.obj (E.inverse.obj N)))))).symm ≪≫
      E'.functor.mapIso (R.app (E.functor.obj (asc.obj (res.obj (E.inverse.obj N)))) ≪≫
        P.mapIso (E.unitIso.app (asc.obj (res.obj (E.inverse.obj N)))).symm) ≪≫
      E'.functor.mapIso (A.app (res.obj (E.inverse.obj N))).symm) ≪≫
    ι' (E'.functor.obj (asc'.obj (p.obj (res.obj (E.inverse.obj N))))) ≪≫
    res'.mapIso (E'.unitIso.app (asc'.obj (p.obj (res.obj (E.inverse.obj N))))).symm ≪≫
    (asIso (adj'.unit.app (p.obj (res.obj (E.inverse.obj N))))).symm ≪≫
    p.mapIso (ι N).symm

/-- The six factors of `Stacks.UnitCounitBaseChange.baseChangeAlongEquivalence` collapse to
`ι'`, the comparison `R`, `Stacks.UnitCounitBaseChange.baseChangeOfCounitUnit` and `ι⁻¹`. -/
theorem baseChangeAlongEquivalence_eq (E : Y ≌ X) (E' : Y' ≌ X') {ρ : X ⥤ Z} {ρ' : X' ⥤ Z'}
    {res : Y ⥤ Z} {asc : Z ⥤ Y} (adj : asc ⊣ res) {res' : Y' ⥤ Z'}
    {asc' : Z' ⥤ Y'} (adj' : asc' ⊣ res') (ι : ∀ N, ρ.obj N ≅ res.obj (E.inverse.obj N))
    (ι' : ∀ N', ρ'.obj N' ≅ res'.obj (E'.inverse.obj N')) {φ : X ⥤ X'} {P : Y ⥤ Y'} {p : Z ⥤ Z'}
    (R : φ ⋙ E'.inverse ≅ E.inverse ⋙ P) (A : p ⋙ asc' ≅ asc ⋙ P)
    (hι' : ∀ {N₁ N₂ : X'} (f : N₁ ⟶ N₂),
      ρ'.map f ≫ (ι' N₂).hom = (ι' N₁).hom ≫ res'.map (E'.inverse.map f)) (N : X)
    [IsIso (adj.counit.app (E.inverse.obj N))]
    [IsIso (adj'.unit.app (p.obj (res.obj (E.inverse.obj N))))] :
    (baseChangeAlongEquivalence E E' adj adj' ι ι' R A N).hom =
      (ι' (φ.obj N)).hom ≫ res'.map ((R.app N).hom) ≫
      baseChangeOfCounitUnit adj adj' A (E.inverse.obj N) ≫ p.map ((ι N).inv) := by
  have key : ∀ {Y₁ : X'} (f : φ.obj N ⟶ Y₁)
      (h : E'.inverse.obj Y₁ ⟶ asc'.obj (p.obj (res.obj (E.inverse.obj N)))),
      E'.inverse.map (f ≫ (E'.counitIso.app Y₁).inv ≫ E'.functor.map h) ≫
        (E'.unitIso.app (asc'.obj (p.obj (res.obj (E.inverse.obj N))))).inv =
      E'.inverse.map f ≫ h := by
    intro Y₁ f h
    simp
  have key2 : E.inverse.map ((E.counitIso.app N).inv ≫
      E.functor.map (inv (adj.counit.app (E.inverse.obj N)))) ≫
      (E.unitIso.app (asc.obj (res.obj (E.inverse.obj N)))).inv =
      inv (adj.counit.app (E.inverse.obj N)) := by
    simp [Equivalence.unit_app_inverse]
  have hX : E'.inverse.map (φ.map ((E.counitIso.app N).inv ≫
        E.functor.map (inv (adj.counit.app (E.inverse.obj N)))) ≫
      (E'.counitIso.app (φ.obj (E.functor.obj (asc.obj (res.obj (E.inverse.obj N)))))).inv ≫
        E'.functor.map ((R.app (E.functor.obj (asc.obj (res.obj (E.inverse.obj N))))).hom ≫
          P.map ((E.unitIso.app (asc.obj (res.obj (E.inverse.obj N)))).inv)) ≫
        E'.functor.map ((A.app (res.obj (E.inverse.obj N))).inv)) ≫
      (E'.unitIso.app (asc'.obj (p.obj (res.obj (E.inverse.obj N))))).inv =
      (R.app N).hom ≫ P.map (inv (adj.counit.app (E.inverse.obj N))) ≫
        (A.app (res.obj (E.inverse.obj N))).inv := by
    rw [← E'.functor.map_comp]
    refine (key _ _).trans ?_
    have n1 := R.hom.naturality ((E.counitIso.app N).inv ≫
      E.functor.map (inv (adj.counit.app (E.inverse.obj N))))
    have n1' : E'.inverse.map (φ.map ((E.counitIso.app N).inv ≫
          E.functor.map (inv (adj.counit.app (E.inverse.obj N))))) ≫
        (R.app (E.functor.obj (asc.obj (res.obj (E.inverse.obj N))))).hom ≫
          P.map ((E.unitIso.app (asc.obj (res.obj (E.inverse.obj N)))).inv) =
        (R.app N).hom ≫ P.map (inv (adj.counit.app (E.inverse.obj N))) :=
      (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ P.map
          ((E.unitIso.app (asc.obj (res.obj (E.inverse.obj N)))).inv)) n1).trans
        ((Category.assoc _ _ _).trans (congrArg (fun t => R.hom.app N ≫ t)
          ((P.map_comp _ _).symm.trans (congrArg P.map key2)))))
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (A.app _).inv) n1').trans
      (Category.assoc _ _ _))
  unfold baseChangeOfCounitUnit baseChangeOfUnit
  show ρ'.map (φ.map ((E.counitIso.app N).inv ≫
      E.functor.map (inv (adj.counit.app (E.inverse.obj N))))) ≫
    ρ'.map ((E'.counitIso.app (φ.obj (E.functor.obj (asc.obj (res.obj (E.inverse.obj N)))))).inv ≫
      E'.functor.map ((R.app (E.functor.obj (asc.obj (res.obj (E.inverse.obj N))))).hom ≫
        P.map ((E.unitIso.app (asc.obj (res.obj (E.inverse.obj N)))).inv)) ≫
      E'.functor.map ((A.app (res.obj (E.inverse.obj N))).inv)) ≫
    (ι' (E'.functor.obj (asc'.obj (p.obj (res.obj (E.inverse.obj N)))))).hom ≫
    res'.map ((E'.unitIso.app (asc'.obj (p.obj (res.obj (E.inverse.obj N))))).inv) ≫
    inv (adj'.unit.app (p.obj (res.obj (E.inverse.obj N)))) ≫
    p.map ((ι N).inv) = _
  dsimp only [Functor.comp_obj]
  rw [← Functor.map_comp_assoc, ← Category.assoc (ρ'.map _), hι', Category.assoc,
    ← Functor.map_comp_assoc res', hX]
  simp only [Functor.map_comp, Category.assoc, Functor.id_obj]

/-- **The comparisons `baseChangeAlongEquivalence` compose.**  Given base changes `φ₁`, `φ₂`, `φ`
on the objects presented by equivalences, `P₁`, `P₂`, `P` on their presentations and `p₁`, `p₂`,
`p` on the targets of the right adjoints, with composition comparisons `cX`, `cY` and `cZ`, if the
comparisons `R` of the presentations compose (`hR`) and the comparisons `A` of the left adjoints
compose (`hA`), then the comparison along `φ` followed by `cZ⁻¹` is the comparison along `φ₁` read
through `cX`, followed by the comparison along `φ₂`. -/
theorem baseChangeAlongEquivalence_comp (E₀ : Y ≌ X) (E₁ : Y' ≌ X') (E₂ : Y'' ≌ X'')
    {ρ₀ : X ⥤ Z} {ρ₁ : X' ⥤ Z'} {ρ₂ : X'' ⥤ Z''}
    {res₀ : Y ⥤ Z} {asc₀ : Z ⥤ Y} (adj₀ : asc₀ ⊣ res₀)
    {res₁ : Y' ⥤ Z'} {asc₁ : Z' ⥤ Y'} (adj₁ : asc₁ ⊣ res₁) {res₂ : Y'' ⥤ Z''} {asc₂ : Z'' ⥤ Y''}
    (adj₂ : asc₂ ⊣ res₂) (ι₀ : ∀ N, ρ₀.obj N ≅ res₀.obj (E₀.inverse.obj N))
    (ι₁ : ∀ N, ρ₁.obj N ≅ res₁.obj (E₁.inverse.obj N))
    (ι₂ : ∀ N, ρ₂.obj N ≅ res₂.obj (E₂.inverse.obj N)) {φ₁ : X ⥤ X'} {φ₂ : X' ⥤ X''} {φ : X ⥤ X''}
    {P₁ : Y ⥤ Y'} {P₂ : Y' ⥤ Y''} {P : Y ⥤ Y''} {p₁ : Z ⥤ Z'} {p₂ : Z' ⥤ Z''} {p : Z ⥤ Z''}
    (R₁ : φ₁ ⋙ E₁.inverse ≅ E₀.inverse ⋙ P₁) (R₂ : φ₂ ⋙ E₂.inverse ≅ E₁.inverse ⋙ P₂)
    (R : φ ⋙ E₂.inverse ≅ E₀.inverse ⋙ P)
    (A₁ : p₁ ⋙ asc₁ ≅ asc₀ ⋙ P₁) (A₂ : p₂ ⋙ asc₂ ≅ asc₁ ⋙ P₂) (A : p ⋙ asc₂ ≅ asc₀ ⋙ P)
    (cX : φ ⟶ φ₁ ⋙ φ₂) (cYR : P ⟶ P₁ ⋙ P₂) (cY : P₁ ⋙ P₂ ≅ P) (cZR : p ⟶ p₁ ⋙ p₂)
    (cZ : p₁ ⋙ p₂ ≅ p)
    (hι₁ : ∀ {N₁ N₂ : X'} (f : N₁ ⟶ N₂),
      ρ₁.map f ≫ (ι₁ N₂).hom = (ι₁ N₁).hom ≫ res₁.map (E₁.inverse.map f))
    (hι₂ : ∀ {N₁ N₂ : X''} (f : N₁ ⟶ N₂),
      ρ₂.map f ≫ (ι₂ N₂).hom = (ι₂ N₁).hom ≫ res₂.map (E₂.inverse.map f))
    (hcY : cYR = cY.inv) (hcZ : cZR = cZ.inv)
    (hR : Functor.whiskerRight cX E₂.inverse ≫ Functor.whiskerLeft φ₁ R₂.hom ≫
        Functor.whiskerRight R₁.hom P₂ = R.hom ≫ Functor.whiskerLeft E₀.inverse cYR)
    (hA : Functor.isoWhiskerLeft p₁ A₂ ≪≫ Functor.isoWhiskerRight A₁ P₂ ≪≫
        Functor.isoWhiskerLeft asc₀ cY = Functor.isoWhiskerRight cZ asc₂ ≪≫ A)
    (N : X) [hc₀ : IsIso (adj₀.counit.app (E₀.inverse.obj N))]
    [hu₀₂ : IsIso (adj₂.unit.app (p.obj (res₀.obj (E₀.inverse.obj N))))]
    [hu₀₁ : IsIso (adj₁.unit.app (p₁.obj (res₀.obj (E₀.inverse.obj N))))]
    [hc₁ : IsIso (adj₁.counit.app (E₁.inverse.obj (φ₁.obj N)))]
    [hu₁₂ : IsIso (adj₂.unit.app (p₂.obj (res₁.obj (E₁.inverse.obj (φ₁.obj N)))))] :
    (baseChangeAlongEquivalence E₀ E₂ adj₀ adj₂ ι₀ ι₂ R A N).hom ≫ cZR.app (ρ₀.obj N) =
      ρ₂.map (cX.app N) ≫ (baseChangeAlongEquivalence E₁ E₂ adj₁ adj₂ ι₁ ι₂ R₂ A₂ (φ₁.obj N)).hom ≫
        p₂.map (baseChangeAlongEquivalence E₀ E₁ adj₀ adj₁ ι₀ ι₁ R₁ A₁ N).hom := by
  subst hcY hcZ
  have : IsIso (adj₁.counit.app (P₁.obj (E₀.inverse.obj N))) :=
    isIso_app_of_iso (c := E₁.inverse.obj (φ₁.obj N)) adj₁.counit (R₁.app N)
  have : IsIso (adj₂.unit.app (p₂.obj (res₁.obj (P₁.obj (E₀.inverse.obj N))))) :=
    isIso_app_of_iso (c := p₂.obj (res₁.obj (E₁.inverse.obj (φ₁.obj N)))) adj₂.unit
      (p₂.mapIso (res₁.mapIso (R₁.app N)))
  have hc := baseChangeOfCounitUnit_comp adj₀ adj₁ adj₂ A₁ A₂ A cY cZ hA (E₀.inverse.obj N)
  have nc : p.map ((ι₀ N).inv) ≫ cZ.inv.app (ρ₀.obj N) =
      cZ.inv.app (res₀.obj (E₀.inverse.obj N)) ≫ p₂.map (p₁.map ((ι₀ N).inv)) :=
    cZ.inv.naturality ((ι₀ N).inv)
  have nι : ρ₂.map (cX.app N) ≫ (ι₂ (φ₂.obj (φ₁.obj N))).hom =
      (ι₂ (φ.obj N)).hom ≫ res₂.map (E₂.inverse.map (cX.app N)) :=
    hι₂ (cX.app N)
  have nδ := baseChangeOfCounitUnit_naturality adj₁ adj₂ A₂ (M := E₁.inverse.obj (φ₁.obj N))
    (M' := P₁.obj (E₀.inverse.obj N)) (R₁.hom.app N)
  have hRN := NatTrans.congr_app hR N
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj] at hRN
  rw [baseChangeAlongEquivalence_eq _ _ _ _ _ _ _ _ hι₂,
    baseChangeAlongEquivalence_eq _ _ _ _ _ _ _ _ hι₂,
    baseChangeAlongEquivalence_eq _ _ _ _ _ _ _ _ hι₁]
  simp only [Category.assoc, Functor.map_comp, Iso.app_hom]
  rw [nc, reassoc_of% hc, reassoc_of% nι, Iso.map_inv_hom_id_assoc, reassoc_of% nδ,
    ← res₂.map_comp_assoc (R.hom.app N), ← hRN]
  simp only [Functor.map_comp, Category.assoc]

end Stacks.UnitCounitBaseChange

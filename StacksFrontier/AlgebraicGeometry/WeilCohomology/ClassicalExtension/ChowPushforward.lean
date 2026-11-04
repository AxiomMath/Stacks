module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Definition
public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.BlowupFormulaHomogeneous
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalExtension.Data
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.EquidimensionalCorrespondence
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GysinOpenImmersion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.GraphAction
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# Proper pushforward of cycles along the connected components

Let `X` be a smooth projective scheme over `k` of constant relative dimension `d`. Its Chow group
graded by codimension, `CH^r(X) = ∏_{d'} CH_{d'-r}(X_{d'})`, has a single nonzero factor, the one
of the part `X_d = X`; reading a class there identifies `CH^r(X)` with `CH_{d-r}(X)`
(`Stacks.WeilCohomology.totalChow`). Under this identification the pushforward between
equidimensional schemes of axiom (C)(b) is proper pushforward of cycles, and the Gysin map of an
open immersion is restriction (Stacks 0FF4). Along the connected components `X_c` of `X`, with
inclusions `ι_c : X_c ⟶ X`:

* `α = ∑_c ι_{c,*}(α|_{X_c})`;
* `f_*(ι_{c,*} β) = ι_{d,*}(f_{c,*} β)` for `f : X ⟶ Y` and its restriction `f_c : X_c ⟶ Y_d`;
* `(ι_{d,*} β)|_{Y_{d'}}` is `β` for `d' = d` and `0` otherwise.

## Main definitions

* `Stacks.WeilCohomology.totalChow`: `CH^r(X) ⟶ CH_{d-r}(X)` for `X` of constant relative
  dimension `d`.
* `Stacks.WeilCohomology.compPushforward`: the pushforward `ι_{i,*} : CH^p(X_i) ⟶ CH^p(X)` along
  the inclusion of a component.

## Main results

* `Stacks.WeilCohomology.totalChow_injective`: `totalChow` is injective for `X` of constant
  relative dimension.
* `Stacks.WeilCohomology.totalChow_equidimensionalPushforward`: the pushforward between
  equidimensional schemes is proper pushforward of cycles.
* `Stacks.WeilCohomology.totalChow_codimensionGysin_of_isOpenImmersion`: the Gysin map of an open
  immersion is restriction of cycles.
* `Stacks.WeilCohomology.sum_compPushforward_restrictChow`: `α = ∑_i ι_{i,*}(α|_{X_i})`.
* `Stacks.WeilCohomology.equidimensionalPushforward_compPushforward`:
  `f_*(ι_{i,*} β) = ι_{j,*}(f_{i,*} β)`.
* `Stacks.WeilCohomology.restrictChow_compPushforward_self`,
  `Stacks.WeilCohomology.restrictChow_compPushforward_of_ne`: `(ι_{i,*} β)|_{Y_{i'}}` is `β` for
  `i' = i` and `0` otherwise.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Chow

universe u

namespace Stacks.WeilCohomology

open SmoothProjectiveScheme
open ClassicalWeilCohomologyTheory (restrictChow)

variable {k : Type u} [Field k]

/-! ### Pushforward along a surjective open immersion -/

/-- Pushforward along a surjective open immersion undoes restriction. -/
theorem properChowPushforward_chowGroupRestrict_of_surjective {Z U : Scheme.{u}}
    (sZ : Z ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sZ]
    (sU : U ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sU] (m : U ⟶ Z)
    [IsOpenImmersion m] [IsProper m] (hsurj : Function.Surjective m.base) (hm : m ≫ sZ = sU)
    (n : ℤ) (hfac : ProperPushforwardFactorsThroughRationalEquivalence _ sU sZ m hm n)
    (x : chowGroup (fieldChowSituation k) sZ n) :
    properChowPushforward _ sU sZ m hm n hfac (chowGroupRestrict _ sZ sU m hm n x) = x := by
  have hdec : IsClopenDecomposition fun _ : PUnit.{u + 1} ↦ m.opensRange :=
    ⟨fun i j h ↦ (h (Subsingleton.elim i j)).elim, by
      rw [iSup_const]
      ext z
      simpa using hsurj z⟩
  refine (chowGroupClopenRestrictEquiv (fieldChowSituation k) sZ (fun _ : PUnit.{u + 1} ↦ sU)
    (fun _ ↦ m) (fun _ ↦ hm) hdec n).injective (funext fun _ ↦ ?_)
  rw [chowGroupClopenRestrictEquiv_apply, chowGroupClopenRestrictEquiv_apply,
    chowGroupRestrict_properChowPushforward_self]

/-! ### Codimension-graded classes on an equidimensional scheme -/

section Total

variable (Z : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)

/-- **`CH^r(Z) ⟶ CH_{d-r}(Z)`**: the class of the part `Z_d`, pushed forward to `Z`. For `Z` of
constant relative dimension `d` this is an isomorphism, `Z_d` being all of `Z`. -/
def totalChow (r : ℤ) :
    codimensionChowGroup k Z.obj.hom r →+ chowGroup (fieldChowSituation k) Z.obj.hom (d - r) :=
  haveI := (isClopenDecomposition_dimPart Z.obj.hom).isProper_ι d
  (properChowPushforward (fieldChowSituation k) (partBase Z.obj.hom d) Z.obj.hom
    (dimPart Z.obj.hom d).ι rfl (d - r) (properPushforwardDescends _ _ _ _ _ _)).comp
    (Pi.evalAddMonoidHom (fun d' : ℕ ↦
      chowGroup (fieldChowSituation k) (partBase Z.obj.hom d') (d' - r)) d)

/-- Restricting `totalChow Z d r β` to the part `Z_d` gives the component `β d`. -/
theorem chowGroupRestrict_totalChow (r : ℤ) (β : codimensionChowGroup k Z.obj.hom r) :
    chowGroupRestrict (fieldChowSituation k) Z.obj.hom (partBase Z.obj.hom d)
      (dimPart Z.obj.hom d).ι rfl (d - r) (totalChow Z d r β) = β d := by
  have := (isClopenDecomposition_dimPart Z.obj.hom).isProper_ι d
  rw [totalChow, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply]
  exact chowGroupRestrict_properChowPushforward_self (fieldChowSituation k) Z.obj.hom
    (partBase Z.obj.hom d) (dimPart Z.obj.hom d).ι rfl (d - r) _ (β d)

variable {Z d}

/-- For `Z` of constant relative dimension `d`, the inclusion of the part `Z_d` is surjective. -/
theorem surjective_dimPart_ι (hZ : RelativeDimension Z.obj.hom d) :
    Function.Surjective (dimPart Z.obj.hom d).ι.base :=
  fun z ↦ ⟨⟨z, by rw [dimPart_self_eq_top Z.obj.hom hZ]; trivial⟩, rfl⟩

/-- For `Z` of constant relative dimension `d`, `totalChow Z d r β = x` when the component `β d`
is the restriction of `x` to the part `Z_d`. -/
theorem totalChow_chowGroupRestrict (hZ : RelativeDimension Z.obj.hom d) (r : ℤ)
    (x : chowGroup (fieldChowSituation k) Z.obj.hom (d - r))
    (β : codimensionChowGroup k Z.obj.hom r)
    (hβ : β d = chowGroupRestrict (fieldChowSituation k) Z.obj.hom (partBase Z.obj.hom d)
      (dimPart Z.obj.hom d).ι rfl (d - r) x) : totalChow Z d r β = x := by
  have := (isClopenDecomposition_dimPart Z.obj.hom).isProper_ι d
  rw [totalChow, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply, hβ]
  exact properChowPushforward_chowGroupRestrict_of_surjective _ _ _ (surjective_dimPart_ι hZ) _ _
    _ _

/-- **`CH^r(Z) ⟶ CH_{d-r}(Z)` is injective** for `Z` of constant relative dimension `d`. -/
theorem totalChow_injective (hZ : RelativeDimension Z.obj.hom d) (r : ℤ) :
    Function.Injective (totalChow Z d r) := by
  intro β β' h
  funext d'
  by_cases hd : d' = d
  · subst hd
    rw [← chowGroupRestrict_totalChow Z _ r β, ← chowGroupRestrict_totalChow Z _ r β', h]
  · have := isEmpty_dimPart_of_ne Z.obj.hom hZ hd
    exact @Subsingleton.elim _ (subsingleton_chowGroup_of_isEmpty _ _ _) _ _

end Total

/-! ### Pushforward and restriction -/

/-- A morphism of smooth projective schemes over `k` is proper as a morphism of schemes. -/
instance isProper_hom_left {X Y : (SmoothProjectiveScheme k).FullSubcategory} (f : X ⟶ Y) :
    IsProper f.hom.left := by
  have : IsProper (f.hom.left ≫ Y.obj.hom) := by rw [Over.w f.hom]; infer_instance
  exact IsProper.of_comp f.hom.left Y.obj.hom

/-- Proper pushforward along a fixed morphism, in equal degrees, respects `HEq` of the classes. -/
private theorem properChowPushforward_heq_of_degree_eq {A B : Scheme.{u}}
    {sA : A ⟶ (fieldChowSituation k).S} [LocallyOfFiniteType sA]
    {sB : B ⟶ (fieldChowSituation k).S} [LocallyOfFiniteType sB] (u : A ⟶ B) [IsProper u]
    (hu : u ≫ sB = sA) {n n' : ℤ} (hn : n = n')
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence _ sA sB u hu n)
    (hfac' : ProperPushforwardFactorsThroughRationalEquivalence _ sA sB u hu n')
    {α : chowGroup (fieldChowSituation k) sA n} {α' : chowGroup (fieldChowSituation k) sA n'}
    (hα : α ≍ α') : properChowPushforward _ sA sB u hu n hfac α ≍
      properChowPushforward _ sA sB u hu n' hfac' α' :=
  properChowPushforward_heq_of_morphism_eq _ u u rfl rfl hu hu hn hfac hfac' hα

/-- **The pushforward between equidimensional schemes is proper pushforward of cycles**, read
through `CH^r ≅ CH_{d-r}`. -/
theorem totalChow_equidimensionalPushforward {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X ⟶ Y) {d e : ℕ} (hY : RelativeDimension Y.obj.hom e) (p q : ℤ) (h : q = p + e - d)
    (α : codimensionChowGroup k X.obj.hom p) :
    totalChow Y e q (equidimensionalPushforward f d e p q h α) =
      chowGroupDegreeEquiv _ _ (by omega)
        (properChowPushforward (fieldChowSituation k) X.obj.hom Y.obj.hom f.hom.left
          (Over.w f.hom) (d - p) (properPushforwardDescends _ _ _ _ _ _) (totalChow X d p α)) := by
  have := (isClopenDecomposition_dimPart X.obj.hom).isProper_ι d
  have := (isClopenDecomposition_dimPart Y.obj.hom).isProper_ι e
  refine eq_of_heq ?_
  refine HEq.trans ?_ (chowGroupDegreeEquiv_heq _ _ _ _).symm
  rw [totalChow, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply,
    equidimensionalPushforward_apply_self f p q h α, totalChow, AddMonoidHom.comp_apply,
    Pi.evalAddMonoidHom_apply]
  have hcomp := DFunLike.congr_fun (properChowPushforward_comp (fieldChowSituation k)
    (partBase X.obj.hom d) X.obj.hom Y.obj.hom (dimPart X.obj.hom d).ι f.hom.left rfl
    (Over.w f.hom) (d - p) (properPushforwardDescends _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _)) (α d)
  rw [AddMonoidHom.comp_apply] at hcomp
  rw [hcomp]
  refine (properChowPushforward_heq_of_degree_eq _ _ (by omega) _
    (properPushforwardDescends _ _ _ _ _ _) (chowGroupDegreeEquiv_heq _ _ _ _)).trans ?_
  rw [properChowPushforward_chowGroupRestrict_of_surjective _ _ _ (surjective_dimPart_ι hY)]

/-- **The Gysin map of an open immersion is restriction of cycles**, read through
`CH^r ≅ CH_{d-r}`. -/
theorem totalChow_codimensionGysin_of_isOpenImmersion
    {U Z : (SmoothProjectiveScheme k).FullSubcategory}
    (j : U ⟶ Z) [IsOpenImmersion j.hom.left] {d : ℕ} (hU : RelativeDimension U.obj.hom d)
    (r : ℤ) (β : codimensionChowGroup k Z.obj.hom r) :
    totalChow U d r (codimensionGysin U.obj.hom Z.obj.hom (Over.w j.hom) r β) =
      chowGroupRestrict (fieldChowSituation k) Z.obj.hom U.obj.hom j.hom.left (Over.w j.hom)
        (d - r) (totalChow Z d r β) := by
  have := (isClopenDecomposition_dimPart Z.obj.hom).isProper_ι d
  refine totalChow_chowGroupRestrict hU r _ _ ?_
  rw [codimensionGysin_of_isOpenImmersion Z.obj.hom U.obj.hom (Over.w j.hom),
    chowGroupRestrict_comp (fieldChowSituation k) Z.obj.hom U.obj.hom j.hom.left (Over.w j.hom)
      (d - r) (partBase U.obj.hom d) (dimPart U.obj.hom d).ι rfl,
    chowGroupRestrict_congr (fieldChowSituation k) Z.obj.hom (partBase U.obj.hom d) _ _ (d - r)
      (dimPartMap Z.obj.hom U.obj.hom (Over.w j.hom) d ≫ (dimPart Z.obj.hom d).ι)
      (dimPartMap_ι _ _ _ _).symm
      (by rw [Category.assoc]; exact dimPartMap_comp_partBase _ _ _ _),
    ← chowGroupRestrict_comp (fieldChowSituation k) Z.obj.hom (partBase Z.obj.hom d)
      (dimPart Z.obj.hom d).ι rfl (d - r) (partBase U.obj.hom d)
      (dimPartMap Z.obj.hom U.obj.hom (Over.w j.hom) d) (dimPartMap_comp_partBase _ _ _ _),
    chowGroupRestrict_totalChow]

/-! ### Decomposition along the connected components -/

section Components

/-- **A cycle class is the sum of its restrictions to the connected components**, pushed
forward. -/
theorem sum_properChowPushforward_chowGroupRestrict_compOpens
    (X : (SmoothProjectiveScheme k).FullSubcategory)
    (n : ℤ) (x : chowGroup (fieldChowSituation k) X.obj.hom n) :
    ∑ c : Components X, properChowPushforward (fieldChowSituation k)
        ((compOpens X c).ι ≫ X.obj.hom) X.obj.hom (compOpens X c).ι rfl n
        (properPushforwardDescends _ _ _ _ _ _)
        (chowGroupRestrict (fieldChowSituation k) X.obj.hom ((compOpens X c).ι ≫ X.obj.hom)
          (compOpens X c).ι rfl n x) = x := by
  have hdec : IsClopenDecomposition fun c : Components X ↦ (compOpens X c).ι.opensRange := by
    simp only [Scheme.Opens.opensRange_ι]
    exact ⟨fun c c' h ↦ X.obj.left.disjoint_connectedComponentOpens h,
      X.obj.left.iSup_connectedComponentOpens⟩
  have hdisj : Pairwise fun c c' : Components X ↦
      Disjoint (Set.range (compOpens X c).ι.base) (Set.range (compOpens X c').ι.base) := by
    intro c c' h
    simp only [Scheme.Opens.range_ι]
    exact Set.disjoint_left.2 fun x (hx : _ = _) (hx' : _ = _) ↦ h (hx.symm.trans hx')
  refine (chowGroupClopenRestrictEquiv (fieldChowSituation k) X.obj.hom
    (fun c : Components X ↦ (compOpens X c).ι ≫ X.obj.hom) (fun c ↦ (compOpens X c).ι)
    (fun _ ↦ rfl) hdec n).injective (funext fun c ↦ ?_)
  rw [chowGroupClopenRestrictEquiv_apply, chowGroupClopenRestrictEquiv_apply]
  exact chowGroupRestrict_sum_properChowPushforward (fieldChowSituation k) X.obj.hom
    (fun c ↦ (compOpens X c).ι ≫ X.obj.hom) (fun c ↦ (compOpens X c).ι) (fun _ ↦ rfl) hdisj n
    (fun c ↦ chowGroupRestrict (fieldChowSituation k) X.obj.hom ((compOpens X c).ι ≫ X.obj.hom)
      (compOpens X c).ι rfl n x) c

variable {X Y : (SmoothProjectiveScheme k).FullSubcategory}

/-- A connected component `X_i` of `X` of constant relative dimension `d` has constant relative
dimension `d`. -/
theorem relativeDimension_compAt {d : ℕ} (hX : RelativeDimension X.obj.hom d) (i : Idx X) :
    RelativeDimension ((SmoothProjective.toSchemeCat k).obj (compAt X i)).obj.hom d :=
  RelativeDimension.comp_isOpenImmersion _ _ hX

variable (X) in
/-- **Pushforward `ι_{i,*} : CH^p(X_i) ⟶ CH^p(X)`** along the inclusion of a component, for `X`
of constant relative dimension `d`. -/
def compPushforward (d : ℕ) (i : Idx X) (p : ℤ) :
    codimensionChowGroup k ((SmoothProjective.toSchemeCat k).obj (compAt X i)).obj.hom p →+
      codimensionChowGroup k X.obj.hom p :=
  equidimensionalPushforward (compAtι X i) d d p p (by ring)

/-- **`ι_{i,*}` is proper pushforward of cycles** along the inclusion of a component, read through
`CH^p ≅ CH_{d-p}`. -/
theorem totalChow_compPushforward {d : ℕ} (hX : RelativeDimension X.obj.hom d) (i : Idx X) (p : ℤ)
    (β : codimensionChowGroup k ((SmoothProjective.toSchemeCat k).obj (compAt X i)).obj.hom p) :
    totalChow X d p (compPushforward X d i p β) =
      properChowPushforward (fieldChowSituation k) _ X.obj.hom (compAtι X i).hom.left
        (Over.w (compAtι X i).hom) (d - p) (properPushforwardDescends _ _ _ _ _ _)
        (totalChow _ d p β) :=
  totalChow_equidimensionalPushforward (compAtι X i) hX p p (by ring) β

/-- **`α = ∑_i ι_{i,*}(α|_{X_i})`** for `X` of constant relative dimension. -/
theorem sum_compPushforward_restrictChow {d : ℕ} (hX : RelativeDimension X.obj.hom d) (p : ℤ)
    (α : codimensionChowGroup k X.obj.hom p) :
    ∑ i, compPushforward X d i p (restrictChow X i p α) = α := by
  refine totalChow_injective hX p ?_
  rw [map_sum]
  simp only [totalChow_compPushforward hX, restrictChow,
    totalChow_codimensionGysin_of_isOpenImmersion _ (relativeDimension_compAt hX _)]
  refine Eq.trans ?_ (sum_properChowPushforward_chowGroupRestrict_compOpens X (d - p)
    (totalChow X d p α))
  exact Equiv.sum_comp (idxEquiv X) (fun c ↦ properChowPushforward (fieldChowSituation k)
    ((compOpens X c).ι ≫ X.obj.hom) X.obj.hom (compOpens X c).ι rfl (d - p)
    (properPushforwardDescends _ _ _ _ _ _)
    (chowGroupRestrict (fieldChowSituation k) X.obj.hom ((compOpens X c).ι ≫ X.obj.hom)
      (compOpens X c).ι rfl (d - p) (totalChow X d p α)))

/-- To show `(ι_{i,*}β)|_{Y_{i'}} = x`, compare the images under `totalChow`. -/
private theorem restrictChow_compPushforward_eq {e : ℕ} (hY : RelativeDimension Y.obj.hom e)
    (i i' : Idx Y) (q : ℤ)
    (β : codimensionChowGroup k ((SmoothProjective.toSchemeCat k).obj (compAt Y i)).obj.hom q)
    (x : codimensionChowGroup k ((SmoothProjective.toSchemeCat k).obj (compAt Y i')).obj.hom q)
    (h : chowGroupRestrict (fieldChowSituation k) Y.obj.hom
      ((SmoothProjective.toSchemeCat k).obj (compAt Y i')).obj.hom
      (compAtι Y i').hom.left (Over.w (compAtι Y i').hom) (e - q)
      (properChowPushforward (fieldChowSituation k) _ Y.obj.hom (compAtι Y i).hom.left
        (Over.w (compAtι Y i).hom) (e - q) (properPushforwardDescends _ _ _ _ _ _)
        (totalChow _ e q β)) = totalChow _ e q x) :
    restrictChow Y i' q (compPushforward Y e i q β) = x := by
  refine totalChow_injective (relativeDimension_compAt hY i') q ?_
  rw [restrictChow,
    totalChow_codimensionGysin_of_isOpenImmersion _ (relativeDimension_compAt hY i'),
    totalChow_compPushforward hY, h]

/-- **`(ι_{i,*}β)|_{Y_i} = β`.** -/
theorem restrictChow_compPushforward_self {e : ℕ} (hY : RelativeDimension Y.obj.hom e) (i : Idx Y)
    (q : ℤ)
    (β : codimensionChowGroup k ((SmoothProjective.toSchemeCat k).obj (compAt Y i)).obj.hom q) :
    restrictChow Y i q (compPushforward Y e i q β) = β :=
  restrictChow_compPushforward_eq hY i i q β β
    (chowGroupRestrict_properChowPushforward_self _ _ _ _ _ _ _ _)

/-- **`(ι_{i,*}β)|_{Y_{i'}} = 0`** for `i' ≠ i`. -/
theorem restrictChow_compPushforward_of_ne {e : ℕ} (hY : RelativeDimension Y.obj.hom e)
    {i i' : Idx Y} (h : i ≠ i') (q : ℤ)
    (β : codimensionChowGroup k ((SmoothProjective.toSchemeCat k).obj (compAt Y i)).obj.hom q) :
    restrictChow Y i' q (compPushforward Y e i q β) = 0 := by
  refine restrictChow_compPushforward_eq hY i i' q β 0 ?_
  rw [map_zero]
  refine chowGroupRestrict_properChowPushforward_of_disjoint _ _ _ _ _ _ _ _ ?_ _ _ _
  simp only [compAtι, compι_left]
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι]
  exact Set.disjoint_left.2 fun x (hx : _ = _) (hx' : _ = _) ↦
    (idxEquiv Y).injective.ne h (hx.symm.trans hx')

/-- **`f_*(ι_{i,*}β) = ι_{j,*}(f_{i,*}β)`** for the restriction `f_i : X_i ⟶ Y_j` of `f`. -/
theorem equidimensionalPushforward_compPushforward (f : X ⟶ Y) {d e : ℕ}
    (hX : RelativeDimension X.obj.hom d) (hY : RelativeDimension Y.obj.hom e) (i : Idx X)
    (p q : ℤ) (h : q = p + e - d)
    (β : codimensionChowGroup k ((SmoothProjective.toSchemeCat k).obj (compAt X i)).obj.hom p) :
    equidimensionalPushforward f d e p q h (compPushforward X d i p β) =
      compPushforward Y e (idxMap f i) q
        (equidimensionalPushforward ((SmoothProjective.toSchemeCat k).map (resIdx f i)) d e p q h
          β) := by
  refine totalChow_injective hY q ?_
  rw [totalChow_equidimensionalPushforward f hY p q h, totalChow_compPushforward hX,
    totalChow_compPushforward hY,
    totalChow_equidimensionalPushforward _ (relativeDimension_compAt hY _) p q h]
  refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans ?_)
  have h1 := DFunLike.congr_fun (properChowPushforward_comp (fieldChowSituation k) _ X.obj.hom
    Y.obj.hom (compAtι X i).hom.left f.hom.left (Over.w (compAtι X i).hom) (Over.w f.hom) (d - p)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _))
    (totalChow _ d p β)
  have h2 := DFunLike.congr_fun (properChowPushforward_comp (fieldChowSituation k) _ _
    Y.obj.hom ((SmoothProjective.toSchemeCat k).map (resIdx f i)).hom.left
    (compAtι Y (idxMap f i)).hom.left (Over.w ((SmoothProjective.toSchemeCat k).map
      (resIdx f i)).hom) (Over.w (compAtι Y (idxMap f i)).hom) (d - p)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _))
    (totalChow _ d p β)
  rw [AddMonoidHom.comp_apply] at h1 h2
  rw [h1]
  refine HEq.symm ?_
  refine (properChowPushforward_heq_of_degree_eq _ _ (show (e : ℤ) - q = d - p by omega) _
    (properPushforwardDescends _ _ _ _ _ _) (chowGroupDegreeEquiv_heq _ _ _ _)).trans ?_
  refine (heq_of_eq h2).trans ?_
  exact properChowPushforward_heq_of_morphism_eq (fieldChowSituation k)
    (((SmoothProjective.toSchemeCat k).map (resIdx f i)).hom.left ≫
      (compAtι Y (idxMap f i)).hom.left) ((compAtι X i).hom.left ≫ f.hom.left)
    (resIdx_left_ι f i) rfl
    (by rw [Category.assoc, Over.w (compAtι Y (idxMap f i)).hom,
      Over.w ((SmoothProjective.toSchemeCat k).map (resIdx f i)).hom])
    (by rw [Category.assoc, Over.w f.hom, Over.w (compAtι X i).hom]) rfl
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _) HEq.rfl

end Components

end Stacks.WeilCohomology

end

module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleColimitUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtalePresentedSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition

/-!
# Cohomology of the inverse images of one sheaf along a limit of schemes

Let `S` be a scheme, let `G` be an abelian sheaf on its small étale site, and let `(X_i)` be a
directed inverse system of quasi-compact and quasi-separated schemes over `S` with affine
transition morphisms and limit `X = lim X_i`. The inverse images `s_i^{-1}G` of `G` to the levels,
with the canonical comparisons along the transitions, form a system of sheaves in the sense of
[Stacks, Tag 0EZL], and the inverse image `s^{-1}G` of `G` to the limit presents its colimit.
[Stacks, Tag 09YQ] then says

`H^p(X, s^{-1}G) = colim_i H^p(X_i, s_i^{-1}G)`.

This is the form in which the source applies Tag 09YQ in Lemma 03Q6 and in the limit arguments
of the section on smooth base change: a class on `S` restricted to the limit vanishes as soon as
it vanishes at some level, and every class on the limit comes from a level.

## Main definitions

* `Stacks.EtaleCohomology.EtaleSheafSystem.ofInverseImage` — a system of sheaves in the sense of
  Tag 0EZL from transition maps out of the constructed inverse image
  `Stacks.EtaleCohomology.etaleAbelianInverseImage`, satisfying the cocycle condition there.
* `Stacks.EtaleCohomology.pullbackSystem` — the system `(s_i^{-1}G)` of inverse images of one
  sheaf on a base.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.pullbackSystemLeg` — the canonical legs
  `f_i^{-1}s_i^{-1}G ≅ s^{-1}G`.

## Main results

* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.isColimitPresentation_pullbackSystem` — the
  inverse image of `G` to the limit presents the colimit of the system.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.exists_restriction_eq_zero_of_isLimit` — a
  class on `S` whose restriction to the limit vanishes already vanishes on some level.
* `Stacks.EtaleCohomology.SmallEtaleLimitCohomology.exists_eq_etaleCohomologyMapTo_of_isLimit` —
  every class on the limit comes from a level.

## Implementation notes

The colimit presentation is formal: every leg is an isomorphism and so is every transition, so
over a nonempty directed index the leg at any one level already exhibits `s^{-1}G` as the
colimit. The two coherences it needs, the cocycle condition of the system and the compatibility
of the legs, are both the associativity pentagon
`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'_assoc`.

## References

* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 03Q6](https://stacks.math.columbia.edu/tag/03Q6)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u

namespace Stacks.EtaleCohomology

section OfInverseImage

variable {I : Type v} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]

/-- **A system of sheaves from transition maps out of the constructed inverse image.** A family
of sheaves on the levels together with maps `t_a : D(a)^{-1}F_j ⟶ F_i`, where the inverse image is
`Stacks.EtaleCohomology.etaleAbelianInverseImage`, satisfying the cocycle condition in that
inverse image, is a system of sheaves in the sense of Tag 0EZL. Its transitions, read back
through `Stacks.EtaleCohomology.systemTransitionMap`, are the given maps
(`EtaleSheafSystem.systemTransitionMap_ofInverseImage`). -/
def EtaleSheafSystem.ofInverseImage (F : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i))
      AddCommGrpCat.{u + 1})
    (t : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (etaleAbelianInverseImage.{u, u + 1} (D.map a)).obj (F j) ⟶ F i)
    (ht : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k),
      (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (D.map b) (D.map (a ≫ b))
          (D.map_comp a b)).hom.app (F k) ≫
        (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (t b) ≫ t a = t (a ≫ b)) :
    EtaleSheafSystem D AddCommGrpCat.{u + 1} where
  obj := F
  map a := (SmallEtaleLimitCohomology.inverseImageIsoPullbackAb (D.map a)).hom.app _ ≫ t a
  map_comp {i j k} a b := by
    have hco := NatTrans.congr_app
      (SmallEtaleLimitCohomology.systemPullbackComp_inv_comp (D := D) a b) (F k)
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at hco
    rw [Functor.map_comp, ← ht a b]
    simp only [Category.assoc]
    rw [(SmallEtaleLimitCohomology.inverseImageIsoPullbackAb (D.map a)).hom.naturality_assoc,
      reassoc_of% hco]

/-- The transitions of `EtaleSheafSystem.ofInverseImage`, read out of the constructed inverse
image, are the maps it was built from. -/
theorem EtaleSheafSystem.systemTransitionMap_ofInverseImage
    (F : ∀ i : Iᵒᵖ, Sheaf (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1})
    (t : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      (etaleAbelianInverseImage.{u, u + 1} (D.map a)).obj (F j) ⟶ F i)
    (ht : ∀ {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k),
      (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (D.map b) (D.map (a ≫ b))
          (D.map_comp a b)).hom.app (F k) ≫
        (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map (t b) ≫ t a = t (a ≫ b))
    {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemTransitionMap (EtaleSheafSystem.ofInverseImage F t ht) a = t a := by
  rw [SmallEtaleLimitCohomology.systemTransitionMap_eq]
  exact Iso.inv_hom_id_app_assoc _ _ _

end OfInverseImage

/-! ### The system of inverse images of one sheaf -/

section MapToId

variable {X Y : Scheme.{u}} (k : Y ⟶ X)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{u + 1}]
  [HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
  [HasExt.{u + 1} (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})]

/-- The cohomology map of a morphism together with the identity of the inverse image is
restriction along the morphism. -/
@[simp]
theorem etaleCohomologyMapTo_id (A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (p : ℕ)
    (x : Sheaf.H.{u + 1, u + 1} A p) :
    etaleCohomologyMapTo k (𝟙 _) p x = etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k A p x :=
  Sheaf.H.map_id_apply _

end MapToId

section PullbackSystem

variable {S : Scheme.{u}} {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology S) AddCommGrpCat.{u + 1}]

/-- The associativity pentagon of the inverse image comparison
`Stacks.EtaleCohomology.etaleAbelianInverseImageCompIso'_assoc`, evaluated at one sheaf, in the
shape of a cocycle condition: comparing along `j` and then along `i`, and then reassembling along
`a = i ≫ f` and `p = j ≫ a`, is reassembling along `q = j ≫ i` and `p = q ≫ f`. -/
theorem etaleAbelianInverseImageCompIso'_hom_app_map_inv_app {X₀ X₁ X₂ X₃ : Scheme.{u}}
    (f : X₁ ⟶ X₀)
    [HasSheafify (smallEtaleTopology X₀) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X₁) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X₂) AddCommGrpCat.{u + 1}]
    [HasSheafify (smallEtaleTopology X₃) AddCommGrpCat.{u + 1}]
    (i : X₂ ⟶ X₁) (j : X₃ ⟶ X₂) (a : X₂ ⟶ X₀) (ha : a = i ≫ f) (q : X₃ ⟶ X₁) (hq : q = j ≫ i)
    (p : X₃ ⟶ X₀) (hp₁ : p = q ≫ f) (hp₂ : p = j ≫ a)
    (G : Sheaf (smallEtaleTopology X₀) AddCommGrpCat.{u + 1}) :
    (etaleAbelianInverseImageCompIso'.{u, u + 1} j i q hq).hom.app
        ((etaleAbelianInverseImage.{u, u + 1} f).obj G) ≫
      (etaleAbelianInverseImage.{u, u + 1} j).map
        ((etaleAbelianInverseImageCompIso'.{u, u + 1} i f a ha).inv.app G) ≫
      (etaleAbelianInverseImageCompIso'.{u, u + 1} j a p hp₂).inv.app G =
    (etaleAbelianInverseImageCompIso'.{u, u + 1} q f p hp₁).inv.app G := by
  have h := congrArg (fun e => e.hom.app G)
    (etaleAbelianInverseImageCompIso'_assoc.{u, u + 1} f i j a ha q hq p hp₁ hp₂)
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_inv_app, Category.id_comp] at h
  rw [← h, Iso.hom_inv_id_app_assoc]

variable (G : Sheaf (smallEtaleTopology S) AddCommGrpCat.{u + 1}) (s : ∀ i : Iᵒᵖ, D.obj i ⟶ S)
  (hs : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), s i = D.map a ≫ s j)

/-- The cocycle condition of the system of inverse images of one sheaf. -/
theorem pullbackSystem_cocycle {i j k : Iᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (D.map b) (D.map (a ≫ b))
        (D.map_comp a b)).hom.app ((etaleAbelianInverseImage.{u, u + 1} (s k)).obj G) ≫
      (etaleAbelianInverseImage.{u, u + 1} (D.map a)).map
        ((etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map b) (s k) (s j) (hs b)).inv.app G) ≫
      (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (s j) (s i) (hs a)).inv.app G =
    (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map (a ≫ b)) (s k) (s i)
      (hs (a ≫ b))).inv.app G :=
  etaleAbelianInverseImageCompIso'_hom_app_map_inv_app (s k) (D.map b) (D.map a) (s j)
    (hs b) (D.map (a ≫ b)) (D.map_comp a b) (s i) (hs (a ≫ b)) (hs a) G

/-- **The system of inverse images of one sheaf.** For an inverse system `(X_i)` of schemes over
`S`, with structure morphisms `s_i`, and an abelian sheaf `G` on `S`, the sheaves `s_i^{-1}G`
with the canonical comparisons `D(a)^{-1}s_j^{-1}G ≅ s_i^{-1}G` form a system of sheaves in the
sense of Tag 0EZL. -/
def pullbackSystem : EtaleSheafSystem D AddCommGrpCat.{u + 1} :=
  EtaleSheafSystem.ofInverseImage (fun i => (etaleAbelianInverseImage.{u, u + 1} (s i)).obj G)
    (fun {i j} a => (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (s j) (s i)
      (hs a)).inv.app G)
    (fun a b => pullbackSystem_cocycle G s hs a b)

/-- The sheaf at level `i` of the system of inverse images of `G` is `s_i^{-1}G`. -/
@[simp]
theorem pullbackSystem_obj (i : Iᵒᵖ) :
    (pullbackSystem G s hs).obj i = (etaleAbelianInverseImage.{u, u + 1} (s i)).obj G := rfl

/-- The transition map of the system of inverse images of `G` along `a : i ⟶ j` is the canonical
comparison `D(a)^{-1}s_j^{-1}G ⟶ s_i^{-1}G`. -/
theorem systemTransitionMap_pullbackSystem {i j : Iᵒᵖ} (a : i ⟶ j) :
    systemTransitionMap (pullbackSystem G s hs) a =
      (etaleAbelianInverseImageCompIso'.{u, u + 1} (D.map a) (s j) (s i) (hs a)).inv.app G :=
  EtaleSheafSystem.systemTransitionMap_ofInverseImage _ _
    (fun a b => pullbackSystem_cocycle G s hs a b) a

end PullbackSystem

/-! ### The colimit presentation and the colimit statement -/

namespace SmallEtaleLimitCohomology

/-- Two maps out of the sources of two isomorphisms related by a common map `d` agree after
precomposing with the inverses. -/
private theorem inv_comp_eq_inv_comp_of_comp_eq {C : Type*} [Category C] {X Y W H : C}
    {X' : C} (d₁ : X ⟶ X') (d₂ : X' ⟶ Y) (li : Y ⟶ W) (lj : X ⟶ W) [IsIso li] [IsIso lj]
    (h₁ : d₁ ≫ d₂ ≫ li = lj) (τi : Y ⟶ H) (τj : X ⟶ H) (h₂ : d₁ ≫ d₂ ≫ τi = τj) :
    inv li ≫ τi = inv lj ≫ τj := by
  have hd : d₁ ≫ d₂ = lj ≫ inv li := by
    rw [← h₁, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← h₂, show inv lj ≫ d₁ ≫ d₂ ≫ τi = inv lj ≫ (d₁ ≫ d₂) ≫ τi by simp, hd,
    Category.assoc, IsIso.inv_hom_id_assoc]

section Presentation

variable {S : Scheme.{u}} {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}
  [∀ i : Iᵒᵖ, HasSheafify (smallEtaleTopology (D.obj i)) AddCommGrpCat.{u + 1}]
  [HasSheafify (smallEtaleTopology S) AddCommGrpCat.{u + 1}]
  (G : Sheaf (smallEtaleTopology S) AddCommGrpCat.{u + 1}) (s : ∀ i : Iᵒᵖ, D.obj i ⟶ S)
  (hs : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), s i = D.map a ≫ s j)
  {c : Cone D} [HasSheafify (smallEtaleTopology c.pt) AddCommGrpCat.{u + 1}]
  (sc : c.pt ⟶ S) (hsc : ∀ i : Iᵒᵖ, sc = conePi c i ≫ s i)

/-- The leg `f_i^{-1}s_i^{-1}G ⟶ s^{-1}G` of the system of inverse images of `G`: the canonical
comparison along `s = s_i ∘ f_i`, an isomorphism. -/
def pullbackSystemLeg (i : Iᵒᵖ) :
    (etaleAbelianInverseImage.{u, u + 1} (conePi c i)).obj ((pullbackSystem G s hs).obj i) ⟶
      (etaleAbelianInverseImage.{u, u + 1} sc).obj G :=
  (etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c i) (s i) sc (hsc i)).inv.app G

/-- Each leg `f_i^{-1}s_i^{-1}G ⟶ s^{-1}G` of the system of inverse images is an isomorphism. -/
instance isIso_pullbackSystemLeg (i : Iᵒᵖ) : IsIso (pullbackSystemLeg G s hs sc hsc i) :=
  inferInstanceAs (IsIso
    ((etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c i) (s i) sc (hsc i)).app G).inv)

/-- The legs of the system of inverse images are compatible with its transitions. -/
theorem isCompatibleFamily_pullbackSystemLeg :
    IsCompatibleFamily (c := c) (pullbackSystem G s hs) _ (pullbackSystemLeg G s hs sc hsc) := by
  intro i j a
  rw [systemTransitionMap_pullbackSystem]
  exact etaleAbelianInverseImageCompIso'_hom_app_map_inv_app (s j) (D.map a) (conePi c i) (s i)
    (hs a) (conePi c j)
    (conePi_comp c a).symm sc (hsc j) (hsc i) G

/-- **The inverse image of `G` to the limit presents the colimit of the system of inverse
images.** Over a nonempty directed index every leg and every transition is an isomorphism, so a
compatible family is determined by its value at any one level, where it factors through the
invertible leg. -/
theorem isColimitPresentation_pullbackSystem [Nonempty I] [IsDirected I (· ≤ ·)] :
    IsColimitPresentation (c := c) (pullbackSystem G s hs) _
      (pullbackSystemLeg G s hs sc hsc) where
  compatible := isCompatibleFamily_pullbackSystemLeg G s hs sc hsc
  existsUnique_desc H τ hτ := by
    -- the family read through the invertible legs does not depend on the level
    have key : ∀ {i j : Iᵒᵖ} (_ : i ⟶ j),
        inv (pullbackSystemLeg G s hs sc hsc i) ≫ τ i =
          inv (pullbackSystemLeg G s hs sc hsc j) ≫ τ j := fun a =>
      inv_comp_eq_inv_comp_of_comp_eq _ _ _ _
        (isCompatibleFamily_pullbackSystemLeg G s hs sc hsc a) _ _ (hτ a)
    have key' : ∀ i j : Iᵒᵖ, inv (pullbackSystemLeg G s hs sc hsc i) ≫ τ i =
        inv (pullbackSystemLeg G s hs sc hsc j) ≫ τ j := by
      intro i j
      obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i.unop j.unop
      exact (key (homOfLE hik).op).symm.trans (key (homOfLE hjk).op)
    let i₀ : Iᵒᵖ := op (Classical.arbitrary I)
    refine ⟨inv (pullbackSystemLeg G s hs sc hsc i₀) ≫ τ i₀, fun i => ?_, fun χ hχ => ?_⟩
    · rw [key' i₀ i, IsIso.hom_inv_id_assoc]
    · rw [← hχ i₀, IsIso.inv_hom_id_assoc]

end Presentation

section Colimit

variable {S : Scheme.{u}} {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  {D : Iᵒᵖ ⥤ Scheme.{u}} [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
  [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)]
  (G : Sheaf (smallEtaleTopology S) AddCommGrpCat.{u + 1}) (s : ∀ i : Iᵒᵖ, D.obj i ⟶ S)
  (hs : ∀ {i j : Iᵒᵖ} (a : i ⟶ j), s i = D.map a ≫ s j)
  {c : Cone D} (hc : IsLimit c) (sc : c.pt ⟶ S) (hsc : ∀ i : Iᵒᵖ, sc = conePi c i ≫ s i)

/-- The system of inverse images of `G`, presented on the limit by the inverse image of `G`. -/
def pullbackPresentedSystem : PresentedSystem (c := c) IsColimitPresentation :=
  presentedSystemOfIsColimitPresentation (pullbackSystem G s hs) _
    (pullbackSystemLeg G s hs sc hsc) (isColimitPresentation_pullbackSystem G s hs sc hsc)

include hc in
/-- **[Stacks, Tag 09YQ] for the inverse images of one sheaf.** Let `(X_i)` be a nonempty
directed inverse system of quasi-compact and quasi-separated schemes over `S` with affine
transition morphisms and limit `X`, and let `G` be an abelian sheaf on the small étale site of
`S`. Then `H^p(X, s^{-1}G) = colim_i H^p(X_i, s_i^{-1}G)`, in the elementwise form of
`IsCohomologyColimit`. -/
theorem isCohomologyColimit_pullbackPresentedSystem (p : ℕ) :
    IsCohomologyColimit (pullbackPresentedSystem G s hs sc hsc) p := by
  have : Small.{u} ↥(Set.range D.obj ∪ {c.pt} : Set Scheme.{u}) := by
    have : Small.{u} ↥(Set.range D.obj) := small_range _
    infer_instance
  obtain ⟨B, hB⟩ :=
    BigEtaleSite.exists_contains_of_small (Set.range D.obj ∪ {c.pt} : Set Scheme.{u})
  exact isCohomologyColimit_of_isLimit.{u, u} D c B (fun i => hB _ (Or.inl ⟨i, rfl⟩))
    (hB _ (Or.inr rfl)) hc p _

/-- Restricting a class along `k₂`, then applying `k₁` with a map `w₁` that undoes the
comparison along `k = k₁ ≫ k₂`, is restricting along `k`. -/
private theorem etaleCohomologyMapTo_restriction_comp {X Y Z : Scheme.{u}} (k₁ : Z ⟶ Y)
    (k₂ : Y ⟶ X) (k : Z ⟶ X) (hk : k = k₁ ≫ k₂)
    {A : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (w₁ : (etaleAbelianInverseImage.{u, u + 1} k₁).obj
        ((etaleAbelianInverseImage.{u, u + 1} k₂).obj A) ⟶
      (etaleAbelianInverseImage.{u, u + 1} k).obj A)
    (hw : (etaleAbelianInverseImageCompIso'.{u, u + 1} k₁ k₂ k hk).hom.app A ≫ w₁ = 𝟙 _)
    (p : ℕ) (ξ : Sheaf.H.{u + 1, u + 1} A p) :
    etaleCohomologyMapTo k₁ w₁ p (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k₂ A p ξ) =
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1} k A p ξ :=
  (congrArg (etaleCohomologyMapTo k₁ w₁ p) (etaleCohomologyMapTo_id k₂ A p ξ).symm).trans
    ((etaleCohomologyMapTo_comp k₁ k₂ k hk (𝟙 _) w₁ (𝟙 _) (by simpa using hw) p ξ).trans
      (etaleCohomologyMapTo_id k A p ξ))

omit [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] in
/-- The leg of the system of inverse images at a level, on the restriction of a class from the
base, is the restriction of that class to the limit. -/
theorem pullbackPresentedSystem_leg_restriction (i : Iᵒᵖ) (p : ℕ)
    (ξ : Sheaf.H.{u + 1, u + 1} G p) :
    (pullbackPresentedSystem G s hs sc hsc).leg i p
        (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (s i) G p ξ) =
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1} sc G p ξ :=
  etaleCohomologyMapTo_restriction_comp (conePi c i) (s i) sc (hsc i)
    (pullbackSystemLeg G s hs sc hsc i) (by simp [pullbackSystemLeg]) p ξ

omit [Nonempty I] [IsDirected I (· ≤ ·)] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (D.map a)]
    [∀ i : Iᵒᵖ, CompactSpace (D.obj i)] [∀ i : Iᵒᵖ, QuasiSeparatedSpace (D.obj i)] in
/-- The transition of the system of inverse images, on the restriction of a class from the base,
is the restriction of that class to the earlier level. -/
theorem etaleCohomologyTransition_pullbackSystem_restriction {i j : Iᵒᵖ} (a : i ⟶ j) (p : ℕ)
    (ξ : Sheaf.H.{u + 1, u + 1} G p) :
    etaleCohomologyTransition (pullbackSystem G s hs) a p
        (etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (s j) G p ξ) =
      etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (s i) G p ξ :=
  etaleCohomologyMapTo_restriction_comp (D.map a) (s j) (s i) (hs a)
    (systemTransitionMap (pullbackSystem G s hs) a)
    (by simp [systemTransitionMap_pullbackSystem]) p ξ

include hs hsc hc in
/-- **A class vanishing on the limit vanishes at a level.** Let `(X_i)` be a nonempty directed
inverse system of quasi-compact and quasi-separated schemes over `S` with affine transition
morphisms and limit `X`, and let `G` be an abelian sheaf on the small étale site of `S`. If the
restriction of `ξ ∈ H^p(S, G)` to `H^p(X, G|_X)` vanishes, then so does its restriction to
`H^p(X_i, G|_{X_i})` for some `i`. This is the injectivity half of
`colim_i H^p(X_i, G|_{X_i}) = H^p(X, G|_X)` ([Stacks, Tag 09YQ]; [Stacks, Tag 03Q6] is the case
of a system of base changes). -/
theorem exists_restriction_eq_zero_of_isLimit (p : ℕ) (ξ : Sheaf.H.{u + 1, u + 1} G p)
    (hξ : etaleCohomologyRestrictionMap.{u, u + 1, u + 1} sc G p ξ = 0) :
    ∃ i : Iᵒᵖ, etaleCohomologyRestrictionMap.{u, u + 1, u + 1} (s i) G p ξ = 0 := by
  let i₀ : Iᵒᵖ := op (Classical.arbitrary I)
  obtain ⟨j, a, hj⟩ := (isCohomologyColimit_pullbackPresentedSystem G s hs hc sc hsc p
    ).exists_transition_eq_zero i₀ _
      ((pullbackPresentedSystem_leg_restriction G s hs sc hsc i₀ p ξ).trans hξ)
  exact ⟨j, (etaleCohomologyTransition_pullbackSystem_restriction G s hs a p ξ).symm.trans hj⟩

include hs hc in
/-- **Every class on the limit comes from a level.** In the situation of
`exists_restriction_eq_zero_of_isLimit`, every class in `H^p(X, G|_X)` is the image, under
restriction along `X ⟶ X_i` followed by the canonical identification of the inverse images, of a
class in `H^p(X_i, G|_{X_i})` for some `i`. This is the surjectivity half of
[Stacks, Tag 09YQ] for the inverse images of one sheaf. -/
theorem exists_eq_etaleCohomologyMapTo_of_isLimit (p : ℕ)
    (y : Sheaf.H.{u + 1, u + 1} ((etaleAbelianInverseImage.{u, u + 1} sc).obj G) p) :
    ∃ (i : Iᵒᵖ) (x : Sheaf.H.{u + 1, u + 1} ((etaleAbelianInverseImage.{u, u + 1} (s i)).obj G) p),
      etaleCohomologyMapTo (conePi c i)
        ((etaleAbelianInverseImageCompIso'.{u, u + 1} (conePi c i) (s i) sc (hsc i)).inv.app G)
        p x = y :=
  (isCohomologyColimit_pullbackPresentedSystem G s hs hc sc hsc p).exists_leg_eq y

end Colimit

end SmallEtaleLimitCohomology

end Stacks.EtaleCohomology

end

module

public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.DescentDatum
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.IsomSheaf

/-!
# A descent datum relative to a covering family, read relative to the sieve it generates

Each arrow of the generated sieve is factored through a member of the family — the factorization is
a choice, and the result does not depend on it up to the gluing isomorphisms — and the object
attached to it is the chosen pullback along that factorization. The gluing isomorphisms are the
transported `CategoryTheory.Functor.DescentDatum.glue` of the family datum, so the cocycle
condition is `CategoryTheory.Functor.DescentDatum.glue_trans` and compatibility with base change is
`CategoryTheory.Functor.DescentDatum.glue_baseChange`.

Effectivity of the family datum then follows from effectivity of the sieve datum: the object
descending the latter receives a strongly cartesian morphism from each `x i`, and those morphisms
are compatible with the gluing isomorphisms because
`CategoryTheory.Functor.DescentDatum.glueIso_comp_kappa` identifies the gluing isomorphisms of the
two data.

## Main definitions

* `CategoryTheory.Functor.DescentDatum.toSieve`, the family datum read as a descent datum relative
  to the sieve the family generates;
* `CategoryTheory.Functor.DescentDatum.kappa`, the comparison between the object `x i` of the
  family datum and the object the generated sieve datum attaches to `f i`.

## Main results

* `CategoryTheory.Functor.DescentDatum.isEffective_of_hasEffectiveDescent`, condition (3) of 02ZI
  from condition (3) of 026F.
-/

@[expose] public section

namespace CategoryTheory

open Limits

universe w v₁ v₂ u₁ u₂

namespace Functor

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

variable {p : 𝒳 ⥤ 𝒞} [p.IsFibered]
variable {U : 𝒞} {I : Type w} {V : I → 𝒞} {f : ∀ i, V i ⟶ U}
  {Vij : I → I → 𝒞} {pr₁ : ∀ i j, Vij i j ⟶ V i} {pr₂ : ∀ i j, Vij i j ⟶ V j}
  {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → 𝒞}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
  (D : DescentDatum p V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃)

variable (idx : ∀ (W : 𝒞) (h : W ⟶ U), (Sieve.ofArrows V f).arrows h → I)
  (arr : ∀ (W : 𝒞) (h : W ⟶ U) (hh : (Sieve.ofArrows V f).arrows h), W ⟶ V (idx W h hh))
  (harr : ∀ (W : 𝒞) (h : W ⟶ U) (hh : (Sieve.ofArrows V f).arrows h),
    arr W h hh ≫ f (idx W h hh) = h)

/-- **A descent datum relative to a covering family, read as one relative to the sieve it
generates.** Each arrow of the sieve is factored through a member of the family (the factorization
is a choice, and the result does not depend on it up to the gluing isomorphisms), and the object
attached to it is the chosen pullback along the chosen factorization. The gluing isomorphisms are
the transported gluing isomorphisms
`CategoryTheory.Functor.DescentDatum.glue` of the family datum, so the cocycle condition is
`CategoryTheory.Functor.DescentDatum.glue_trans` and compatibility with base change is
`CategoryTheory.Functor.DescentDatum.glue_baseChange`. -/
@[implicit_reducible]
noncomputable def DescentDatum.toSieve : SieveDescentDatum p (Sieve.ofArrows V f) where
  obj {W} h hh := pullbackFiber p (Fiber.mk (D.hx (idx W h hh))) (arr W h hh)
  iso {W W' Z} {h} hh {g} hg ε ε' heq :=
    pullbackFiberCompIso (Fiber.mk (D.hx (idx W h hh))) (arr W h hh) ε ≪≫
      D.glue (idx W h hh) (idx W' g hg) (ε ≫ arr W h hh) (ε' ≫ arr W' g hg)
        (by simp only [Category.assoc, harr]; exact heq) ≪≫
      (pullbackFiberCompIso (Fiber.mk (D.hx (idx W' g hg))) (arr W' g hg) ε').symm
  cocycle := by
    intro W₁ W₂ W₃ Z h₁ hh₁ h₂ hh₂ h₃ hh₃ ε₁ ε₂ ε₃ e₁₂ e₂₃ e₁₃
    have htr := D.glue_trans (idx W₁ h₁ hh₁) (idx W₂ h₂ hh₂) (idx W₃ h₃ hh₃)
      (ε₁ ≫ arr W₁ h₁ hh₁) (ε₂ ≫ arr W₂ h₂ hh₂) (ε₃ ≫ arr W₃ h₃ hh₃)
      (by simp only [Category.assoc, harr]; exact e₁₂)
      (by simp only [Category.assoc, harr]; exact e₂₃)
      (by simp only [Category.assoc, harr]; exact e₁₃)
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← htr]
    simp [Category.assoc]
  iso_pullback := by
    intro W₁ W₂ Z Z' h₁ hh₁ h₂ hh₂ ε ε' heq γ
    rw [baseChangeFiberMor_eq_iso_pullback]
    simp only [Iso.trans_hom, Iso.symm_hom, ← pullbackFiberCompIso'_rfl]
    rw [baseChangeFiberMor_comp _ _ γ _ _ ((γ ≫ ε) ≫ arr W₁ h₁ hh₁)
        (Category.assoc _ _ _).symm _ _,
      baseChangeFiberMor_comp _ _ γ _ _ ((γ ≫ ε') ≫ arr W₂ h₂ hh₂)
        (Category.assoc _ _ _).symm _ _,
      baseChangeFiberMor_pullbackFiberCompIso' _ _ ε (ε ≫ arr W₁ h₁ hh₁) rfl γ (γ ≫ ε) rfl
        ((γ ≫ ε) ≫ arr W₁ h₁ hh₁) rfl (Category.assoc _ _ _).symm,
      D.glue_baseChange (idx W₁ h₁ hh₁) (idx W₂ h₂ hh₂) (ε ≫ arr W₁ h₁ hh₁)
        (ε' ≫ arr W₂ h₂ hh₂) _ γ ((γ ≫ ε) ≫ arr W₁ h₁ hh₁) (Category.assoc _ _ _).symm
        ((γ ≫ ε') ≫ arr W₂ h₂ hh₂) (Category.assoc _ _ _).symm
        (by simp only [Category.assoc, harr]; rw [heq]),
      ← baseChangeFiberIso_inv,
      baseChangeFiberIso_pullbackFiberCompIso' _ _ ε' (ε' ≫ arr W₂ h₂ hh₂) rfl γ (γ ≫ ε') rfl
        ((γ ≫ ε') ≫ arr W₂ h₂ hh₂) rfl (Category.assoc _ _ _).symm]

/-- The object that the sieve datum generated by a family datum attaches to an arrow `h` of the
generated sieve is the chosen pullback of `x i` along the chosen factorization of `h` through
`f i`. -/
@[simp]
lemma DescentDatum.toSieve_obj {W : 𝒞} (h : W ⟶ U) (hh : (Sieve.ofArrows V f).arrows h) :
    (D.toSieve idx arr harr).obj h hh =
      pullbackFiber p (Fiber.mk (D.hx (idx W h hh))) (arr W h hh) := rfl

/-- The gluing isomorphism of the sieve datum generated by a family datum is the transported gluing
isomorphism `CategoryTheory.Functor.DescentDatum.glue`, conjugated by the contractions of the
iterated chosen pullbacks. -/
lemma DescentDatum.toSieve_iso {W W' Z : 𝒞} {h : W ⟶ U} (hh : (Sieve.ofArrows V f).arrows h)
    {g : W' ⟶ U} (hg : (Sieve.ofArrows V f).arrows g) (ε : Z ⟶ W) (ε' : Z ⟶ W')
    (heq : ε ≫ h = ε' ≫ g) (huv : (ε ≫ arr W h hh) ≫ f (idx W h hh) =
      (ε' ≫ arr W' g hg) ≫ f (idx W' g hg)) :
    (D.toSieve idx arr harr).iso hh hg ε ε' heq =
      pullbackFiberCompIso (Fiber.mk (D.hx (idx W h hh))) (arr W h hh) ε ≪≫
        D.glue (idx W h hh) (idx W' g hg) (ε ≫ arr W h hh) (ε' ≫ arr W' g hg) huv ≪≫
        (pullbackFiberCompIso (Fiber.mk (D.hx (idx W' g hg))) (arr W' g hg) ε').symm := rfl

/-- The comparison between the object `x i` of the family datum and the object that the generated
sieve datum attaches to the member `f i` of the family. -/
noncomputable def DescentDatum.kappa (i : I) :
    (Fiber.mk (D.hx i) : p.Fiber (V i)) ≅
      (D.toSieve idx arr harr).obj (f i) (Sieve.ofArrows_mk V f i) :=
  (pullbackFiberIdIso (Fiber.mk (D.hx i))).symm ≪≫
    (D.glue (idx (V i) (f i) (Sieve.ofArrows_mk V f i)) i
      (arr (V i) (f i) (Sieve.ofArrows_mk V f i)) (𝟙 (V i))
      (by rw [harr, Category.id_comp])).symm

/-- The chosen factorization of `h` through `f i`, precomposed with `ε`, lies over `ε ≫ h`. -/
private lemma comp_arr_comp_f
    (harr : ∀ W h hh, arr W h hh ≫ f (idx W h hh) = h) {W : 𝒞} (h : W ⟶ U)
    (hh : (Sieve.ofArrows V f).arrows h) {Z : 𝒞} (ε : Z ⟶ W) :
    (ε ≫ arr W h hh) ≫ f (idx W h hh) = ε ≫ h := by
  rw [Category.assoc, harr]

/-- Base change of the comparison `CategoryTheory.Functor.DescentDatum.kappa`. -/
lemma DescentDatum.pullbackFiberHom_kappa (i : I) {Z : 𝒞} (γ : Z ⟶ V i) :
    pullbackFiberHom (D.kappa idx arr harr i).hom γ =
      (D.glue i (idx (V i) (f i) (Sieve.ofArrows_mk V f i)) γ
        (γ ≫ arr (V i) (f i) (Sieve.ofArrows_mk V f i))
        (by simp [Category.assoc, harr])).hom ≫
      (pullbackFiberCompIso (Fiber.mk (D.hx (idx (V i) (f i) (Sieve.ofArrows_mk V f i))))
        (arr (V i) (f i) (Sieve.ofArrows_mk V f i)) γ).inv := by
  rw [DescentDatum.kappa]
  simp only [Iso.trans_hom, Iso.symm_hom, pullbackFiberHom_comp]
  rw [pullbackFiberHom_pullbackFiberIdIso_inv_eq,
    ← D.glue_symm (idx (V i) (f i) (Sieve.ofArrows_mk V f i)) i
      (arr (V i) (f i) (Sieve.ofArrows_mk V f i)) (𝟙 (V i)) (by rw [harr, Category.id_comp]),
    D.pullbackFiberHom_glue i (idx (V i) (f i) (Sieve.ofArrows_mk V f i)) (𝟙 (V i))
      (arr (V i) (f i) (Sieve.ofArrows_mk V f i)) (by rw [harr, Category.id_comp]) γ γ
      (Category.comp_id γ) (γ ≫ arr (V i) (f i) (Sieve.ofArrows_mk V f i)) rfl
      (comp_arr_comp_f idx arr harr (f i) (Sieve.ofArrows_mk V f i) γ).symm,
    ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  simp [pullbackFiberCompIso'_rfl]

/-- The comparisons `CategoryTheory.Functor.DescentDatum.kappa` intertwine the gluing isomorphism
of the family datum with the gluing isomorphism of the generated sieve datum. -/
lemma DescentDatum.glueIso_comp_kappa (i j : I) :
    (D.glueIso i j).hom ≫ pullbackFiberHom (D.kappa idx arr harr j).hom (pr₂ i j) =
      pullbackFiberHom (D.kappa idx arr harr i).hom (pr₁ i j) ≫
        ((D.toSieve idx arr harr).iso (Sieve.ofArrows_mk V f i) (Sieve.ofArrows_mk V f j)
          (pr₁ i j) (pr₂ i j) (hVij i j).w).hom := by
  have hw := (hVij i j).w
  have e1 := comp_arr_comp_f idx arr harr (f i) (Sieve.ofArrows_mk V f i) (pr₁ i j)
  have e2 := comp_arr_comp_f idx arr harr (f j) (Sieve.ofArrows_mk V f j) (pr₂ i j)
  rw [D.pullbackFiberHom_kappa idx arr harr i (pr₁ i j),
    D.pullbackFiberHom_kappa idx arr harr j (pr₂ i j), D.glueIso_eq_glue i j,
    D.toSieve_iso idx arr harr (Sieve.ofArrows_mk V f i) (Sieve.ofArrows_mk V f j) (pr₁ i j)
      (pr₂ i j) hw (by rw [e1, e2]; exact hw)]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc,
    D.glue_trans i j (idx (V j) (f j) (Sieve.ofArrows_mk V f j)) (pr₁ i j) (pr₂ i j)
      (pr₂ i j ≫ arr (V j) (f j) (Sieve.ofArrows_mk V f j)) hw e2.symm (by rw [e2]; exact hw),
    ← Category.assoc,
    D.glue_trans i (idx (V i) (f i) (Sieve.ofArrows_mk V f i))
      (idx (V j) (f j) (Sieve.ofArrows_mk V f j))
      (pr₁ i j) (pr₁ i j ≫ arr (V i) (f i) (Sieve.ofArrows_mk V f i))
      (pr₂ i j ≫ arr (V j) (f j) (Sieve.ofArrows_mk V f j)) e1.symm (by rw [e1, e2]; exact hw)
      (by rw [e2]; exact hw)]

set_option backward.isDefEq.respectTransparency false in
/-- **Condition (3) of Stacks 02ZI, from condition (3) of Stacks 026F.** For a functor whose
descent data relative to covering *sieves* are effective, every descent datum relative to a
covering *family* with genuine fibre-product overlaps is effective.

The family datum is read as a datum relative to the sieve it generates
(`CategoryTheory.Functor.DescentDatum.toSieve`), which is effective by hypothesis; the resulting
object `x₀` receives a strongly cartesian morphism from each `x i`, and those morphisms are
compatible with the gluing isomorphisms because
`CategoryTheory.Functor.DescentDatum.glueIso_comp_kappa` identifies the gluing isomorphisms of the
two data. Both canonical comparisons that the source's effectiveness condition asks for are then
the identity, respectively the gluing isomorphism itself. -/
theorem DescentDatum.isEffective_of_hasEffectiveDescent {J : GrothendieckTopology 𝒞}
    (hdesc : HasEffectiveDescent p J) (hf : Sieve.ofArrows V f ∈ J U) : D.IsEffective := by
  have hex : ∀ (W : 𝒞) (h : W ⟶ U), (Sieve.ofArrows V f).arrows h →
      ∃ (i : I) (a : W ⟶ V i), a ≫ f i = h := fun _ _ hh => exists_factorization_of_ofArrows hh
  choose idx arr harr using hex
  obtain ⟨x₀, ζ, hζcart, hζcompat⟩ := hdesc (Sieve.ofArrows V f) hf (D.toSieve idx arr harr)
  -- the comparison morphisms `x i ⟶ x₀` are strongly cartesian over `f i`
  have hν : ∀ i, p.IsStronglyCartesian (f i)
      (Fiber.fiberInclusion.map (D.kappa idx arr harr i).hom ≫
        ζ (f i) (Sieve.ofArrows_mk V f i)) := by
    intro i
    have h0 : p.IsHomLift (𝟙 (V i))
        (Fiber.fiberInclusion.mapIso (D.kappa idx arr harr i)).hom :=
      (D.kappa idx arr harr i).hom.2
    have h1 : p.IsStronglyCartesian (𝟙 (V i))
        (Fiber.fiberInclusion.map (D.kappa idx arr harr i).hom) :=
      IsStronglyCartesian.of_iso p (𝟙 (V i))
        (Fiber.fiberInclusion.mapIso (D.kappa idx arr harr i))
    have h2 : p.IsCartesian (f i) (ζ (f i) (Sieve.ofArrows_mk V f i)) := hζcart _ _
    have h3 : p.IsStronglyCartesian (𝟙 (V i) ≫ f i)
        (Fiber.fiberInclusion.map (D.kappa idx arr harr i).hom ≫
          ζ (f i) (Sieve.ofArrows_mk V f i)) := inferInstance
    rwa [Category.id_comp] at h3
  -- the comparisons are compatible with the gluing isomorphisms of the datum
  have hkey : ∀ i j, D.φ i j ≫ (D.xrji i j).hom ≫
      (Fiber.fiberInclusion.map (D.kappa idx arr harr j).hom ≫
        ζ (f j) (Sieve.ofArrows_mk V f j)) =
      (D.xrij i j).hom ≫ (Fiber.fiberInclusion.map (D.kappa idx arr harr i).hom ≫
        ζ (f i) (Sieve.ofArrows_mk V f i)) := by
    intro i j
    have hA : Fiber.fiberInclusion.map ((D.xrij i j).fiberIso.symm ≪≫
          pullbackFiberIso (D.kappa idx arr harr i) (pr₁ i j)).hom ≫
        IsPreFibered.pullbackMap
          ((D.toSieve idx arr harr).obj (f i) (Sieve.ofArrows_mk V f i)).2 (pr₁ i j) =
        (D.xrij i j).hom ≫ Fiber.fiberInclusion.map (D.kappa idx arr harr i).hom := by
      simp [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, Functor.map_comp,
        Category.assoc, pullbackFiberHom_fac, Restriction.fiberIso_inv_fac_assoc]
    have hB : Fiber.fiberInclusion.map (fibreIsoMk (D.φ_fibreHom i j) (D.φ_iso i j) ≪≫
          (D.xrji i j).fiberIso.symm ≪≫
          pullbackFiberIso (D.kappa idx arr harr j) (pr₂ i j)).hom ≫
        IsPreFibered.pullbackMap
          ((D.toSieve idx arr harr).obj (f j) (Sieve.ofArrows_mk V f j)).2 (pr₂ i j) =
        D.φ i j ≫ (D.xrji i j).hom ≫
          Fiber.fiberInclusion.map (D.kappa idx arr harr j).hom := by
      simp [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, Functor.map_comp,
        Category.assoc, pullbackFiberHom_fac, Restriction.fiberIso_inv_fac_assoc,
        fibreIsoMk_hom, fiberInclusion_map_fibreHomMk]
    have hC : (fibreIsoMk (D.φ_fibreHom i j) (D.φ_iso i j) ≪≫ (D.xrji i j).fiberIso.symm ≪≫
          pullbackFiberIso (D.kappa idx arr harr j) (pr₂ i j)).hom =
        ((D.xrij i j).fiberIso.symm ≪≫
            pullbackFiberIso (D.kappa idx arr harr i) (pr₁ i j)).hom ≫
          ((D.toSieve idx arr harr).iso (Sieve.ofArrows_mk V f i) (Sieve.ofArrows_mk V f j)
            (pr₁ i j) (pr₂ i j) (hVij i j).w).hom := by
      simp only [Iso.trans_hom, Iso.symm_hom, pullbackFiberIso_hom, fibreIsoMk_hom,
        Category.assoc]
      rw [← D.glueIso_comp_kappa idx arr harr i j, DescentDatum.glueIso_hom,
        Restriction.fiberMor]
      simp [Category.assoc, Iso.inv_hom_id_assoc]
    have hcompat := hζcompat (Sieve.ofArrows_mk V f i) (Sieve.ofArrows_mk V f j) (pr₁ i j) (pr₂ i j)
      (hVij i j).w
    have step : (D.φ i j ≫ (D.xrji i j).hom ≫
        Fiber.fiberInclusion.map (D.kappa idx arr harr j).hom) ≫
          ζ (f j) (Sieve.ofArrows_mk V f j) =
        ((D.xrij i j).hom ≫ Fiber.fiberInclusion.map (D.kappa idx arr harr i).hom) ≫
          ζ (f i) (Sieve.ofArrows_mk V f i) := by
      rw [← hA, ← hB, hC, Functor.map_comp]
      simp only [Category.assoc]
      rw [hcompat]
    simpa only [Category.assoc] using step
  -- assemble the effectiveness data
  refine ⟨x₀.1, x₀.2, fun i => Restriction.ofCartesian (D.hx i) x₀.2 _ (hν i),
    fun i => 𝟙 (D.x i), fun i => fibreHom_of_isHomLift_id _ _ (IsHomLift.id (D.hx i)),
    fun i => IsIso.id (D.x i), fun i j => ?_⟩
  have hcart : p.IsStronglyCartesian (pr₁ i j ≫ f i) ((D.xrij i j).hom ≫
      (Fiber.fiberInclusion.map (D.kappa idx arr harr i).hom ≫
        ζ (f i) (Sieve.ofArrows_mk V f i))) := by
    have h1 := (D.xrij i j).isStronglyCartesian_hom
    have h2 := hν i
    exact inferInstance
  have hid : ∀ {k : I} {g : Vij i j ⟶ V k} (r : Restriction p g (D.x k) (D.hx k)),
      r.hom = Restriction.compTo p g (𝟙 (V k)) (by simp) (Restriction.id p (D.x k) (D.hx k)) r :=
    fun r => Restriction.eq_compTo _ (𝟙 _) (by simp) (Restriction.id p _ _) r r.hom
      r.isHomLift_hom (Category.comp_id _)
  refine ⟨Restriction.ofCartesian (D.xrij i j).hpt x₀.2 _ hcart,
    𝟙 (D.xrij i j).pt, D.φ i j,
    fibreHom_of_isHomLift_id _ _ (IsHomLift.id (D.xrij i j).hpt), D.φ_fibreHom i j,
    IsIso.id (D.xrij i j).pt, D.φ_iso i j, ?_, ?_, Category.id_comp _⟩
  · have c1 := hid (D.xrij i j)
    have c2 : (D.xrij i j).hom = Restriction.compTo p (pr₁ i j) (f i) rfl
        (Restriction.ofCartesian (D.hx i) x₀.2 _ (hν i))
        (Restriction.ofCartesian (D.xrij i j).hpt x₀.2 _ hcart) :=
      Restriction.eq_compTo (pr₁ i j) (f i) rfl
        (Restriction.ofCartesian (D.hx i) x₀.2 _ (hν i))
        (Restriction.ofCartesian (D.xrij i j).hpt x₀.2 _ hcart) (D.xrij i j).hom
        (D.xrij i j).isHomLift_hom rfl
    unfold IsRestrictionOf
    rw [← c1, ← c2]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have hφlift : p.IsHomLift (pr₂ i j) (D.φ i j ≫ (D.xrji i j).hom) := by
      have h1 : p.IsHomLift (𝟙 (Vij i j)) (D.φ i j) := (fibreHomMk (D.φ_fibreHom i j)).2
      have h2 : p.IsHomLift (pr₂ i j) ((D.xrji i j).hom) := (D.xrji i j).isHomLift_hom
      exact isHomLift_of_eq (n := 𝟙 (Vij i j) ≫ pr₂ i j) inferInstance (by simp)
    have c3 := hid (D.xrji i j)
    have c4 : D.φ i j ≫ (D.xrji i j).hom = Restriction.compTo p (pr₂ i j) (f j) (hVij i j).w
        (Restriction.ofCartesian (D.hx j) x₀.2 _ (hν j))
        (Restriction.ofCartesian (D.xrij i j).hpt x₀.2 _ hcart) :=
      Restriction.eq_compTo (pr₂ i j) (f j) (hVij i j).w
        (Restriction.ofCartesian (D.hx j) x₀.2 _ (hν j))
        (Restriction.ofCartesian (D.xrij i j).hpt x₀.2 _ hcart) (D.φ i j ≫ (D.xrji i j).hom)
        hφlift (by rw [Category.assoc]; exact hkey i j)
    unfold IsRestrictionOf
    rw [← c3, ← c4]
    exact (Category.comp_id (D.φ i j ≫ (D.xrji i j).hom)).symm

end Functor

end CategoryTheory

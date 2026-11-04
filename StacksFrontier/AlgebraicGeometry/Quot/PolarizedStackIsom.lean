module

public import StacksFrontier.AlgebraicGeometry.Descent.FpqcHomSheafRefinement
public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.ZariskiTransitionExists
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesTransport
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedIsomSheaf
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStack
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.DisjointGluing
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Continuous
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Precoverage

/-!
# Gluing morphisms of polarized families (the `Isom` condition of Stacks 0D40)

Condition (2) of Stacks 02ZI for the category `Polarized` of polarized families of Stacks 0D1M
over the big fppf site: a family of isomorphisms between the restrictions of two polarized
families to the members of a covering, agreeing on the double overlaps, glues to a unique
isomorphism. The source proves it ("by descent for quasi-coherent sheaves") for the line
bundles; the morphisms of total spaces glue because the fpqc topology on schemes is
subcanonical.

## Main results

* `AlgebraicGeometry.existsUnique_comp_eq_of_mem_fpqcTopology`: morphisms of schemes glue along
  a family generating an fpqc covering sieve.
* `AlgebraicGeometry.existsUnique_map_eq_of_mem_fpqcTopology`: morphisms of quasi-coherent
  modules glue along a family generating an fpqc covering sieve (Stacks 023T, full
  faithfulness, in sieve form).
* `AlgebraicGeometry.PolarizedFamily.existsUnique_glue`: morphisms of polarized families glue
  along coverings of their total spaces with cartesian double overlaps.
* `AlgebraicGeometry.polarizedProjection_isomIsSheafFor`: **the `Isom` condition of Stacks 02ZI
  for polarized families** over the big fppf site, the descent of morphisms in the proof of
  Stacks 0D40.

## References

* [Stacks Project, Tag 0D40](https://stacks.math.columbia.edu/tag/0D40)
* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u

namespace AlgebraicGeometry

/-! ### Gluing along a family generating an fpqc covering sieve -/

section Gluing

variable {X : Scheme.{u}} {I : Type w} {Xi : I → Scheme.{u}} (a : ∀ i, Xi i ⟶ X)

/-- Morphisms of schemes glue along a family generating an fpqc covering sieve: the fpqc
topology on schemes is subcanonical. -/
theorem existsUnique_comp_eq_of_mem_fpqcTopology
    (ha : Sieve.ofArrows Xi a ∈ Scheme.fpqcTopology X) {Y : Scheme.{u}} (t : ∀ i, Xi i ⟶ Y)
    (ht : ∀ (i j : I) (Z : Scheme.{u}) (u : Z ⟶ Xi i) (v : Z ⟶ Xi j),
      u ≫ a i = v ≫ a j → u ≫ t i = v ≫ t j) :
    ∃! s : X ⟶ Y, ∀ i, a i ≫ s = t i := by
  have hY := GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
    (J := Scheme.fpqcTopology.{u}) (yoneda.obj Y)
  have h := (Presieve.isSheafFor_iff_generate _).2 (hY _ ha)
  exact (Presieve.isSheafFor_arrows_iff _ _).1 h t fun i j Z u v huv => ht i j Z u v huv

variable (M N : modulePullbackPseudofunctor.obj (.mk (op X)))

/-- The presheaf of morphisms between two quasi-coherent modules satisfies the sheaf condition
for a family generating an fpqc covering sieve, read on the terminal object of the schemes over
the base (Stacks 023T, full faithfulness, in sieve form). -/
theorem isSheafFor_presheafHom_of_mem_fpqcTopology
    (ha : Sieve.ofArrows Xi a ∈ Scheme.fpqcTopology X) (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent) :
    Presieve.IsSheafFor (modulePullbackPseudofunctor.presheafHom M N) (X := Over.mk (𝟙 X))
      (Presieve.ofArrows (fun i ↦ Over.mk (a i))
        (fun i ↦ (Over.homMk (a i) : Over.mk (a i) ⟶ Over.mk (𝟙 X)))) := by
  have := hM
  have := hN
  have hsheaf := isSheaf_presheafHom' (S := X) M N
  rw [isSheaf_iff_isSheaf_of_type] at hsheaf
  have hmem := GrothendieckTopology.overEquiv_symm_mem_over _ (Over.mk (𝟙 X)) _ ha
  rw [overEquiv_symm_ofArrows a] at hmem
  exact (Presieve.isSheafFor_iff_generate _).2 (hsheaf _ hmem)

/-- Morphisms of quasi-coherent modules glue along a family generating an fpqc covering sieve:
the full-faithfulness half of Stacks 023T in sieve form. A family of morphisms
`β i : (a i)^* M ⟶ (a i)^* N` whose restrictions along any two morphisms `u`, `v` with
`u ≫ a i = v ≫ a j` agree is the family of inverse images of a unique `τ : M ⟶ N`. -/
theorem existsUnique_map_eq_of_mem_fpqcTopology
    (ha : Sieve.ofArrows Xi a ∈ Scheme.fpqcTopology X) (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent) (β : ∀ i, pullMod (a i) M ⟶ pullMod (a i) N)
    (hβ : ∀ {Y : Scheme.{u}} (y : Y ⟶ X) (i₁ i₂ : I) (d₁ : Y ⟶ Xi i₁) (d₂ : Y ⟶ Xi i₂)
      (hd₁ : d₁ ≫ a i₁ = y) (hd₂ : d₂ ≫ a i₂ = y),
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (β i₁) d₁ y y hd₁ hd₁ =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom (β i₂) d₂ y y hd₂ hd₂) :
    ∃! τ : M ⟶ N, ∀ i,
      (modulePullbackPseudofunctor.map (a i).op.toLoc).toFunctor.map τ = β i := by
  have hbij := (Pseudofunctor.bijective_toDescentData_map_iff
    (F := modulePullbackPseudofunctor) a M N).mpr
    (isSheafFor_presheafHom_of_mem_fpqcTopology a M N ha hM hN)
  let D : (modulePullbackPseudofunctor.toDescentData a).obj M ⟶
      (modulePullbackPseudofunctor.toDescentData a).obj N :=
    Pseudofunctor.DescentData.subtypeCompatibleHomEquiv modulePullbackPseudofunctor a
      ⟨β, fun i₁ i₂ Z d₁ d₂ _ ↦
        (QuasicoherentDescentData.presheafHom_map_eq M N (a i₁) Z d₁ (β i₁)).trans
          ((hβ Z.hom i₁ i₂ d₁.left d₂.left (Over.w d₁) (Over.w d₂)).trans
            (QuasicoherentDescentData.presheafHom_map_eq M N (a i₂) Z d₂ (β i₂)).symm)⟩
  have hD : ∀ i, D.hom i = β i := fun i ↦ rfl
  obtain ⟨τ, hτ⟩ := hbij.2 D
  refine ⟨τ, fun i ↦ (congrArg (fun ρ : (modulePullbackPseudofunctor.toDescentData a).obj M ⟶
      (modulePullbackPseudofunctor.toDescentData a).obj N ↦ ρ.hom i) hτ).trans (hD i), ?_⟩
  intro τ' hτ'
  apply hbij.1
  rw [hτ]
  ext i
  exact (hτ' i).trans (hD i).symm

/-- Two morphisms of schemes agreeing on the members of a family generating an fpqc covering
sieve are equal. -/
theorem eq_of_comp_eq_of_mem_fpqcTopology
    (ha : Sieve.ofArrows Xi a ∈ Scheme.fpqcTopology X) {Y : Scheme.{u}} (s₁ s₂ : X ⟶ Y)
    (h : ∀ i, a i ≫ s₁ = a i ≫ s₂) : s₁ = s₂ :=
  (existsUnique_comp_eq_of_mem_fpqcTopology a ha (fun i ↦ a i ≫ s₁)
    (fun _ _ _ u v huv ↦ by rw [reassoc_of% huv])).unique (fun _ ↦ rfl) (fun i ↦ (h i).symm)

/-- Two morphisms of quasi-coherent modules agreeing after pullback to the members of a family
generating an fpqc covering sieve are equal. -/
theorem eq_of_map_eq_of_mem_fpqcTopology
    (ha : Sieve.ofArrows Xi a ∈ Scheme.fpqcTopology X) (hM : M.IsQuasicoherent)
    (hN : N.IsQuasicoherent) (τ₁ τ₂ : M ⟶ N)
    (h : ∀ i, (modulePullbackPseudofunctor.map (a i).op.toLoc).toFunctor.map τ₁ =
      (modulePullbackPseudofunctor.map (a i).op.toLoc).toFunctor.map τ₂) : τ₁ = τ₂ := by
  have hbij := (Pseudofunctor.bijective_toDescentData_map_iff
    (F := modulePullbackPseudofunctor) a M N).mpr
    (isSheafFor_presheafHom_of_mem_fpqcTopology a M N ha hM hN)
  apply hbij.1
  ext i
  exact h i

end Gluing

/-! ### Base changes of coverings of the big fppf site -/

section BaseChange

variable (B : BigFppfSite.{u})

/-- The base change of a covering of the big fppf site along any morphism of schemes generates an
fpqc covering sieve. Let `{b i : S i ⟶ S}` generate a covering sieve of the big fppf site, let
`π : X ⟶ S` be a morphism of schemes and let `a i : X i ⟶ X` be the base change of `b i` along
`π`, presented by cartesian squares. Then the family `{a i}` generates an fpqc covering sieve of
`X`. -/
theorem mem_fpqcTopology_of_isPullback {S : B.Schemes} {I : Type w} {Si : I → B.Schemes}
    (b : ∀ i, Si i ⟶ S) (hb : Sieve.ofArrows Si b ∈ B.topology S) {X : Scheme.{u}}
    (π : X ⟶ B.inclusion.obj S) {Xi : I → Scheme.{u}} (a : ∀ i, Xi i ⟶ X)
    (πi : ∀ i, Xi i ⟶ B.inclusion.obj (Si i))
    (hsq : ∀ i, IsPullback (a i) (πi i) π (B.inclusion.map (b i))) :
    Sieve.ofArrows Xi a ∈ Scheme.fpqcTopology X := by
  obtain ⟨E, hE, hle⟩ := exists_covering_le_of_mem_topology B hb
  have hgen : Sieve.generate (E.presieve₀.map B.inclusion) ∈
      Scheme.fppfTopology (B.inclusion.obj S) := by
    have h := BigFppfSite.precoverage_le_comap_fppfTopology B S ⟨E, rfl, hE⟩
    rwa [Precoverage.mem_comap_iff, GrothendieckTopology.mem_toPrecoverage_iff] at h
  refine Scheme.fppfTopology_le_fpqcTopology _ <|
    Scheme.fppfTopology.superset_covering ?_ (Scheme.fppfTopology.pullback_stable π hgen)
  rintro T h ⟨Z, g, f', hf', hfac⟩
  cases hf' with
  | of hr =>
    obtain ⟨Y, k, _, ⟨i⟩, hk⟩ := hle _ _ hr
    refine ⟨Xi i, (hsq i).lift h (g ≫ B.inclusion.map k) ?_, a i, ⟨i⟩, (hsq i).lift_fst _ _ _⟩
    rw [← hfac, Category.assoc, ← B.inclusion.map_comp, hk]

/-- The cartesian square of total spaces over a cartesian square of bases. Let `cᵢ : Xᵢ ⟶ X` and
`cⱼ : Xⱼ ⟶ X` be morphisms of schemes over a morphism of bases, each the base change of its
base, and let `e₁ : W ⟶ Xᵢ`, `e₂ : W ⟶ Xⱼ` be base changes of the two projections of a cartesian
square of bases with `e₁ ≫ cᵢ = e₂ ≫ cⱼ`. Then the square of total spaces is cartesian. -/
theorem isPullback_of_isPullback_base {W Xi Xj X W₀ S₀i S₀j S₀ : Scheme.{u}}
    {e₁ : W ⟶ Xi} {e₂ : W ⟶ Xj} {ci : Xi ⟶ X} {cj : Xj ⟶ X}
    {πW : W ⟶ W₀} {πi : Xi ⟶ S₀i} {πj : Xj ⟶ S₀j} {π : X ⟶ S₀}
    {p₁ : W₀ ⟶ S₀i} {p₂ : W₀ ⟶ S₀j} {bi : S₀i ⟶ S₀} {bj : S₀j ⟶ S₀}
    (h₁ : IsPullback e₁ πW πi p₁) (h₂ : CommSq e₂ πW πj p₂)
    (hi : CommSq ci πi π bi) (hj : IsPullback cj πj π bj)
    (hbase : IsPullback p₁ p₂ bi bj) (he : e₁ ≫ ci = e₂ ≫ cj) :
    IsPullback e₁ e₂ ci cj := by
  have hout : IsPullback e₁ (πW ≫ p₂) (πi ≫ bi) bj := h₁.paste_vert hbase
  rw [← h₂.w, ← hi.w] at hout
  exact IsPullback.of_bot hout he hj

end BaseChange

/-! ### Comparing the polarizations of two families through a morphism of total spaces -/

section Polarized

/-- **The associativity coherence of the pullback of modules, with a reparenthesised
composite.** For `f : A ⟶ B'`, `g : B' ⟶ C`, `h : C ⟶ D` and `e = g ≫ h`, identifying
`f^* g^* h^* M` with `(f ≫ g)^* h^* M` and then with `(f ≫ e)^* M` agrees with identifying
`f^* g^* h^* M` with `f^* e^* M` and then with `(f ≫ e)^* M`. This is a component of
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity`. -/
theorem Scheme.Modules.pullbackComp_inv_map_pullbackComp_hom_congr {A B' C D : Scheme.{u}}
    (f : A ⟶ B') (g : B' ⟶ C) (h : C ⟶ D) (e : B' ⟶ D)
    (he : g ≫ h = e) (M : D.Modules) :
    (Scheme.Modules.pullbackComp f g).inv.app ((Scheme.Modules.pullback h).obj M) ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).hom.app M) ≫
      (Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackCongr he).hom.app M) =
    (Scheme.Modules.pullbackComp (f ≫ g) h).hom.app M ≫
      (Scheme.Modules.pullbackCongr (by rw [Category.assoc, he])).hom.app M ≫
      (Scheme.Modules.pullbackComp f e).inv.app M := by
  subst he
  have H := congrArg (fun α => α.app M) (Scheme.Modules.pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at H
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    CategoryTheory.Functor.map_id, Category.comp_id, eqToIso.hom, eqToHom_app]
  rw [← cancel_mono ((Scheme.Modules.pullbackComp f (g ≫ h)).hom.app M)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← cancel_epi ((Scheme.Modules.pullbackComp f g).hom.app ((Scheme.Modules.pullback h).obj M)),
    Iso.hom_inv_id_app_assoc,
    ← cancel_epi ((Scheme.Modules.pullback f).map ((Scheme.Modules.pullbackComp g h).inv.app M)),
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    ← cancel_epi ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M), Iso.inv_hom_id_app,
    reassoc_of% H]
  simp

namespace PolarizedFamily

variable {B : BigFppfSite.{u}}

/-- The inverse of the polarization of a composite of morphisms of polarized families. -/
theorem comp_lineBundleIso_inv {X Y Z : PolarizedFamily B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).lineBundleIso.inv =
      f.lineBundleIso.inv ≫ (Scheme.Modules.pullback f.totalMap).map g.lineBundleIso.inv ≫
        (Scheme.Modules.pullbackComp f.totalMap g.totalMap).hom.app Z.lineBundle :=
  rfl

/-- Let `t : x.total ⟶ y.total` and let `m : z ⟶ x`, `n : z ⟶ y` be morphisms of polarized
families with `m.totalMap ≫ t = n.totalMap`. The comparison of the pullbacks along
`m.totalMap` of `t^* L_y` and of `L_x`: both are identified with the polarization of `z`, by
`n` and by `m` respectively. -/
def lineBundleComparisonIso {x y z : PolarizedFamily B} (t : x.total ⟶ y.total) (m : z ⟶ x)
    (n : z ⟶ y) (h : m.totalMap ≫ t = n.totalMap) :
    (Scheme.Modules.pullback m.totalMap).obj ((Scheme.Modules.pullback t).obj y.lineBundle) ≅
      (Scheme.Modules.pullback m.totalMap).obj x.lineBundle :=
  (Scheme.Modules.pullbackComp m.totalMap t).app y.lineBundle ≪≫
    (Scheme.Modules.pullbackCongr h).app y.lineBundle ≪≫ n.lineBundleIso ≪≫
      m.lineBundleIso.symm

/-- **The comparison is natural.** Restricting the comparison for `(m, n)` along a morphism
`k : w ⟶ z` of polarized families is the comparison for `(k ≫ m, k ≫ n)`. -/
theorem lineBundleComparisonIso_comp {x y z w : PolarizedFamily B} (t : x.total ⟶ y.total)
    (m : z ⟶ x) (n : z ⟶ y) (h : m.totalMap ≫ t = n.totalMap) (k : w ⟶ z) :
    (Scheme.Modules.pullbackComp k.totalMap m.totalMap).inv.app
        ((Scheme.Modules.pullback t).obj y.lineBundle) ≫
      (Scheme.Modules.pullback k.totalMap).map (lineBundleComparisonIso t m n h).hom ≫
      (Scheme.Modules.pullbackComp k.totalMap m.totalMap).hom.app x.lineBundle =
    (lineBundleComparisonIso t (k ≫ m) (k ≫ n)
      (by rw [comp_totalMap, comp_totalMap, Category.assoc, h])).hom := by
  have hc := Scheme.Modules.pullbackComp_inv_map_pullbackComp_hom_congr k.totalMap m.totalMap t
    n.totalMap h y.lineBundle
  calc _ = (Scheme.Modules.pullbackComp (k.totalMap ≫ m.totalMap) t).hom.app y.lineBundle ≫
        (Scheme.Modules.pullbackCongr (by rw [Category.assoc, h])).hom.app y.lineBundle ≫
        ((Scheme.Modules.pullbackComp k.totalMap n.totalMap).inv.app y.lineBundle ≫
          (Scheme.Modules.pullback k.totalMap).map n.lineBundleIso.hom ≫ k.lineBundleIso.hom) ≫
        (k.lineBundleIso.inv ≫ (Scheme.Modules.pullback k.totalMap).map m.lineBundleIso.inv ≫
          (Scheme.Modules.pullbackComp k.totalMap m.totalMap).hom.app x.lineBundle) := by
        simp only [lineBundleComparisonIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
          Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
        rw [reassoc_of% hc]
    _ = _ := rfl

/-- Two identifications of inverse images along equal morphisms compose to the identification
along the composite equality. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackCongr_hom_app_trans {X Y : Scheme.{u}}
    {f f' f'' : X ⟶ Y} (h₁ : f = f') (h₂ : f' = f'') (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h₁).hom.app M ≫ (Scheme.Modules.pullbackCongr h₂).hom.app M =
      (Scheme.Modules.pullbackCongr (h₁.trans h₂)).hom.app M := by
  subst h₁ h₂
  simp [Scheme.Modules.pullbackCongr]

/-- The identification of inverse images along equal morphisms, at a module, is an `eqToIso`. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.pullbackCongr_app_eq_eqToIso {X Y : Scheme.{u}}
    {f f' : X ⟶ Y} (h : f = f') (M : Y.Modules) :
    (Scheme.Modules.pullbackCongr h).app M = eqToIso (by rw [h]) := by
  subst h
  ext1
  simp [Scheme.Modules.pullbackCongr]

/-- The polarization of a composite, with the identification of the inverse image along the
map of total spaces of the composite with the inverse image along the composite of the maps of
total spaces made explicit. -/
theorem comp_lineBundleIso_hom' {X Y Z : PolarizedFamily B} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).lineBundleIso.hom =
      (Scheme.Modules.pullbackCongr (comp_totalMap f g)).hom.app Z.lineBundle ≫
        (Scheme.Modules.pullbackComp f.totalMap g.totalMap).inv.app Z.lineBundle ≫
        (Scheme.Modules.pullback f.totalMap).map g.lineBundleIso.hom ≫ f.lineBundleIso.hom :=
  (Category.id_comp _).symm

/-- The comparison for a composite: if `n = m ≫ g`, the comparison of `m` and `n` through
`g.totalMap` is the pullback along `m.totalMap` of the polarization of `g`. -/
theorem lineBundleComparisonIso_hom_of_comp {x y z : PolarizedFamily B} (m : z ⟶ x) (g : x ⟶ y)
    (n : z ⟶ y) (hn : m ≫ g = n) (h : m.totalMap ≫ g.totalMap = n.totalMap) :
    (lineBundleComparisonIso g.totalMap m n h).hom =
      (Scheme.Modules.pullback m.totalMap).map g.lineBundleIso.hom := by
  subst hn
  simp only [lineBundleComparisonIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom]
  rw [comp_lineBundleIso_hom']
  simp only [Category.assoc]
  rw [reassoc_of% Scheme.Modules.pullbackCongr_hom_app_trans,
    (show ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (h : f = f) (M : Y.Modules),
      (Scheme.Modules.pullbackCongr h).hom.app M = 𝟙 _ from fun _ _ ↦ rfl), Category.id_comp]
  simp only [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id, Category.comp_id]

/-- **A morphism of polarized families factors another one exactly when the polarizations
compare.** For `m : z ⟶ x`, `g : x ⟶ y` and `n : z ⟶ y` whose base maps and maps of total
spaces compose, `m ≫ g = n` if and only if the pullback of the polarization of `g` along
`m.totalMap` is the comparison of `m` and `n`. -/
theorem comp_eq_iff {x y z : PolarizedFamily B} (m : z ⟶ x) (g : x ⟶ y) (n : z ⟶ y)
    (hb : m.baseMap ≫ g.baseMap = n.baseMap) (h : m.totalMap ≫ g.totalMap = n.totalMap) :
    m ≫ g = n ↔ (Scheme.Modules.pullback m.totalMap).map g.lineBundleIso.hom =
      (lineBundleComparisonIso g.totalMap m n h).hom := by
  refine ⟨fun hn ↦ (lineBundleComparisonIso_hom_of_comp m g n hn h).symm, fun hL ↦ ?_⟩
  refine Hom.ext hb h ?_
  have key : (m ≫ g).lineBundleIso =
      (Scheme.Modules.pullbackCongr h).app y.lineBundle ≪≫ n.lineBundleIso := by
    refine Iso.ext ?_
    rw [Iso.trans_hom, comp_lineBundleIso_hom', hL]
    simp only [lineBundleComparisonIso, Iso.trans_hom, Iso.app_hom, Iso.symm_hom,
      Iso.inv_hom_id_app_assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [reassoc_of% Scheme.Modules.pullbackCongr_hom_app_trans]
    rfl
  rw [key, Scheme.Modules.pullbackCongr_app_eq_eqToIso h y.lineBundle]
  exact eqToIso_trans_heq _ _

/-- `pullHom` only depends on the morphism it restricts along, not on how that morphism is
written. -/
theorem _root_.AlgebraicGeometry.pullHom_congr_left {Y Z₁ : Scheme.{u}} {f₁ : Y ⟶ Z₁}
    {M N : modulePullbackPseudofunctor.obj (.mk (op Z₁))}
    (φ : pullMod f₁ M ⟶ pullMod f₁ N) {Y' : Scheme.{u}} {g g' : Y' ⟶ Y} (hg : g = g')
    (gf : Y' ⟶ Z₁) (h : g ≫ f₁ = gf) (h' : g' ≫ f₁ = gf) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g gf gf h h =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom φ g' gf gf h' h' := by
  subst hg
  rfl

/-- The restriction of the comparison of `(m, n)` along the map of total spaces of a morphism
`k : w ⟶ z` of polarized families is the comparison of `(k ≫ m, k ≫ n)`, in the `pullHom`
spelling. -/
theorem pullHom_lineBundleComparisonIso {x y z w : PolarizedFamily B} (t : x.total ⟶ y.total)
    (m : z ⟶ x) (n : z ⟶ y) (h : m.totalMap ≫ t = n.totalMap) (k : w ⟶ z) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulePullbackPseudofunctor)
        (lineBundleComparisonIso t m n h).hom k.totalMap (k.totalMap ≫ m.totalMap)
          (k.totalMap ≫ m.totalMap) rfl rfl =
      (lineBundleComparisonIso t (k ≫ m) (k ≫ n)
        (by rw [comp_totalMap, comp_totalMap, Category.assoc, h])).hom := by
  refine (modulePullbackPseudofunctor_pullHom k.totalMap m.totalMap _ rfl _ _ _).trans
    (Eq.trans ?_ (lineBundleComparisonIso_comp t m n h k))
  rw [(show ∀ {X Y : Scheme.{u}} {f : X ⟶ Y} (h : f = f) (M : Y.Modules),
      (Scheme.Modules.pullbackCongr h).hom.app M = 𝟙 _ from fun _ _ ↦ rfl)]
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_inv, NatTrans.id_app,
    Category.id_comp, Category.comp_id]
  rfl

/-- The comparison only depends on the two morphisms, not on how they are written. -/
theorem pullHom_lineBundleComparisonIso_congr {x y z : PolarizedFamily B} (t : x.total ⟶ y.total)
    {m m' : z ⟶ x} {n n' : z ⟶ y} (hm : m = m') (hn : n = n') (h : m.totalMap ≫ t = n.totalMap)
    (h' : m'.totalMap ≫ t = n'.totalMap) {Y : Scheme.{u}} (d : Y ⟶ z.total) (yy : Y ⟶ x.total)
    (hd : d ≫ m.totalMap = yy) (hd' : d ≫ m'.totalMap = yy) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulePullbackPseudofunctor)
        (lineBundleComparisonIso t m n h).hom d yy yy hd hd =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulePullbackPseudofunctor)
        (lineBundleComparisonIso t m' n' h').hom d yy yy hd' hd' := by
  subst hm hn
  rfl

/-- Pulling back the inverse of an isomorphism and then the isomorphism gives the identity. -/
theorem _root_.AlgebraicGeometry.pullHom_inv_comp_hom {Y Z : Scheme.{u}} {f : Y ⟶ Z}
    {M N : modulePullbackPseudofunctor.obj (.mk (op Z))} (e : pullMod f M ≅ pullMod f N)
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) (gf : Y' ⟶ Z) (h : g ≫ f = gf) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom e.inv g gf gf h h ≫
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom e.hom g gf gf h h = 𝟙 _ := by
  rw [← pullHom_comp, e.inv_hom_id, pullHom_one]

/-- Pulling back an isomorphism and then its inverse gives the identity. -/
theorem _root_.AlgebraicGeometry.pullHom_hom_comp_inv {Y Z : Scheme.{u}} {f : Y ⟶ Z}
    {M N : modulePullbackPseudofunctor.obj (.mk (op Z))} (e : pullMod f M ≅ pullMod f N)
    {Y' : Scheme.{u}} (g : Y' ⟶ Y) (gf : Y' ⟶ Z) (h : g ≫ f = gf) :
    Pseudofunctor.LocallyDiscreteOpToCat.pullHom e.hom g gf gf h h ≫
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom e.inv g gf gf h h = 𝟙 _ := by
  rw [← pullHom_comp, e.hom_inv_id, pullHom_one]

/-- Maps of total spaces glue along a covering with cartesian double overlaps. -/
private theorem existsUnique_totalMap_comp_eq {x y : PolarizedFamily B} {I : Type w}
    {a : I → PolarizedFamily B} {W : I → I → PolarizedFamily B} (c : ∀ i, a i ⟶ x)
    (hc : Sieve.ofArrows (fun i ↦ (a i).total) (fun i ↦ (c i).totalMap) ∈
      Scheme.fpqcTopology x.total)
    (e₁ : ∀ i j, W i j ⟶ a i) (e₂ : ∀ i j, W i j ⟶ a j)
    (hp : ∀ i j, IsPullback (e₁ i j).totalMap (e₂ i j).totalMap (c i).totalMap (c j).totalMap)
    (ψ : ∀ i, a i ⟶ y) (hψ : ∀ i j, e₁ i j ≫ ψ i = e₂ i j ≫ ψ j) :
    ∃! s : x.total ⟶ y.total, ∀ i, (c i).totalMap ≫ s = (ψ i).totalMap :=
  existsUnique_comp_eq_of_mem_fpqcTopology _ hc _ fun i j Z u v huv ↦ by
    obtain ⟨k, hk₁, hk₂⟩ : ∃ k, k ≫ _ = u ∧ k ≫ _ = v :=
      ⟨_, (hp i j).lift_fst u v huv, (hp i j).lift_snd u v huv⟩
    rw [← hk₁, ← hk₂, Category.assoc, Category.assoc, ← comp_totalMap, ← comp_totalMap, hψ]

/-- **Gluing morphisms of polarized families.** Let `x`, `y` be polarized families over the
same base, let `cx i : ax i ⟶ x` and `cy i : ay i ⟶ y` be morphisms whose maps of total spaces
generate fpqc covering sieves, with double overlaps `Wx i j`, `Wy i j` whose maps of total
spaces are cartesian, and let `φ i : ax i ⟶ ay i` be isomorphisms over the base agreeing on the
double overlaps through isomorphisms `γ i j`. Then there is a unique morphism `g : x ⟶ y` over
the identity of the base with `cx i ≫ g = φ i ≫ cy i` for every `i`. -/
theorem existsUnique_glue {x y : PolarizedFamily B} (hy : y.base = x.base) {I : Type w}
    {ax ay : I → PolarizedFamily B} (cx : ∀ i, ax i ⟶ x) (cy : ∀ i, ay i ⟶ y)
    (φ : ∀ i, ax i ⟶ ay i) [∀ i, IsIso (φ i)]
    (hb : ∀ i, (φ i).baseMap ≫ (cy i).baseMap = (cx i).baseMap ≫ eqToHom hy.symm)
    (hcx : Sieve.ofArrows (fun i ↦ (ax i).total) (fun i ↦ (cx i).totalMap) ∈
      Scheme.fpqcTopology x.total)
    (hcy : Sieve.ofArrows (fun i ↦ (ay i).total) (fun i ↦ (cy i).totalMap) ∈
      Scheme.fpqcTopology y.total)
    {Wx Wy : I → I → PolarizedFamily B}
    (ex₁ : ∀ i j, Wx i j ⟶ ax i) (ex₂ : ∀ i j, Wx i j ⟶ ax j)
    (hex : ∀ i j, ex₁ i j ≫ cx i = ex₂ i j ≫ cx j)
    (hpx : ∀ i j, IsPullback (ex₁ i j).totalMap (ex₂ i j).totalMap (cx i).totalMap
      (cx j).totalMap)
    (ey₁ : ∀ i j, Wy i j ⟶ ay i) (ey₂ : ∀ i j, Wy i j ⟶ ay j)
    (hey : ∀ i j, ey₁ i j ≫ cy i = ey₂ i j ≫ cy j)
    (hpy : ∀ i j, IsPullback (ey₁ i j).totalMap (ey₂ i j).totalMap (cy i).totalMap
      (cy j).totalMap)
    (γ : ∀ i j, Wx i j ⟶ Wy i j) [∀ i j, IsIso (γ i j)]
    (hγ₁ : ∀ i j, γ i j ≫ ey₁ i j = ex₁ i j ≫ φ i)
    (hγ₂ : ∀ i j, γ i j ≫ ey₂ i j = ex₂ i j ≫ φ j) :
    ∃! g : x ⟶ y, g.baseMap = eqToHom hy.symm ∧ ∀ i, cx i ≫ g = φ i ≫ cy i := by
  -- the composites `ψ i = φ i ≫ cy i` agree on the double overlaps of `x`
  have hψ : ∀ i j, ex₁ i j ≫ (φ i ≫ cy i) = ex₂ i j ≫ (φ j ≫ cy j) := by
    intro i j
    rw [← reassoc_of% (hγ₁ i j), ← reassoc_of% (hγ₂ i j), hey]
  -- the composites `inv (φ i) ≫ cx i` agree on the double overlaps of `y`
  have hinv : ∀ i j, ey₁ i j ≫ (inv (φ i) ≫ cx i) = ey₂ i j ≫ (inv (φ j) ≫ cx j) := by
    intro i j
    have e₁ : ey₁ i j ≫ inv (φ i) = inv (γ i j) ≫ ex₁ i j := by
      rw [IsIso.eq_inv_comp, reassoc_of% (hγ₁ i j), IsIso.hom_inv_id, Category.comp_id]
    have e₂ : ey₂ i j ≫ inv (φ j) = inv (γ i j) ≫ ex₂ i j := by
      rw [IsIso.eq_inv_comp, reassoc_of% (hγ₂ i j), IsIso.hom_inv_id, Category.comp_id]
    rw [reassoc_of% e₁, reassoc_of% e₂, hex]
  -- the map of total spaces and its inverse
  obtain ⟨t, ht, -⟩ := existsUnique_totalMap_comp_eq cx hcx ex₁ ex₂ hpx (fun i ↦ φ i ≫ cy i) hψ
  obtain ⟨s, hs, -⟩ :=
    existsUnique_totalMap_comp_eq cy hcy ey₁ ey₂ hpy (fun i ↦ inv (φ i) ≫ cx i) hinv
  have hts : t ≫ s = 𝟙 _ := eq_of_comp_eq_of_mem_fpqcTopology _ hcx _ _ fun i ↦ by
    rw [reassoc_of% (ht i), comp_totalMap, Category.assoc, hs i, ← comp_totalMap,
      IsIso.hom_inv_id_assoc, Category.comp_id]
  have hst : s ≫ t = 𝟙 _ := eq_of_comp_eq_of_mem_fpqcTopology _ hcy _ _ fun i ↦ by
    rw [reassoc_of% (hs i), comp_totalMap, Category.assoc, ht i, ← comp_totalMap,
      IsIso.inv_hom_id_assoc, Category.comp_id]
  have : IsIso t := ⟨⟨s, hts, hst⟩⟩
  -- the square of structure morphisms is cartesian
  have hw : t ≫ y.toBase = x.toBase ≫ B.inclusion.map (eqToHom hy.symm) :=
    eq_of_comp_eq_of_mem_fpqcTopology _ hcx _ _ fun i ↦ by
      rw [reassoc_of% (ht i), (φ i ≫ cy i).cartesian.w, comp_baseMap, hb,
        B.inclusion.map_comp, ← reassoc_of% (cx i).cartesian.w]
  have hcart : IsPullback t x.toBase y.toBase (B.inclusion.map (eqToHom hy.symm)) :=
    IsPullback.of_horiz_isIso ⟨hw⟩
  -- the polarizations
  have hqc : ∀ z : PolarizedFamily B, z.lineBundle.IsQuasicoherent := fun z ↦ by
    let := z.invertible
    exact Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule z.lineBundle
  have hN := hqc x
  have hM : ((Scheme.Modules.pullback t).obj y.lineBundle).IsQuasicoherent := by
    have := hqc y
    infer_instance
  have hΘ : ∀ {Y : Scheme.{u}} (yy : Y ⟶ x.total) (i₁ i₂ : I) (d₁ : Y ⟶ (ax i₁).total)
      (d₂ : Y ⟶ (ax i₂).total) (hd₁ : d₁ ≫ (cx i₁).totalMap = yy)
      (hd₂ : d₂ ≫ (cx i₂).totalMap = yy),
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulePullbackPseudofunctor)
          (lineBundleComparisonIso t (cx i₁) (φ i₁ ≫ cy i₁) (ht i₁)).hom d₁ yy yy hd₁ hd₁ =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulePullbackPseudofunctor)
          (lineBundleComparisonIso t (cx i₂) (φ i₂ ≫ cy i₂) (ht i₂)).hom d₂ yy yy hd₂ hd₂ := by
    intro Y yy i₁ i₂ d₁ d₂ hd₁ hd₂
    obtain ⟨k, h₁, h₂⟩ : ∃ k, k ≫ (ex₁ i₁ i₂).totalMap = d₁ ∧ k ≫ (ex₂ i₁ i₂).totalMap = d₂ :=
      ⟨_, (hpx i₁ i₂).lift_fst _ _ (hd₁.trans hd₂.symm),
        (hpx i₁ i₂).lift_snd _ _ (hd₁.trans hd₂.symm)⟩
    subst h₁ h₂
    have hy₁ : k ≫ (ex₁ i₁ i₂).totalMap ≫ (cx i₁).totalMap = yy := by
      rw [← Category.assoc]; exact hd₁
    have hy₂ : k ≫ (ex₂ i₁ i₂).totalMap ≫ (cx i₂).totalMap = yy := by
      rw [← Category.assoc]; exact hd₂
    have n₁ := pullHom_lineBundleComparisonIso t (cx i₁) (φ i₁ ≫ cy i₁) (ht i₁) (ex₁ i₁ i₂)
    have n₂ := pullHom_lineBundleComparisonIso t (cx i₂) (φ i₂ ≫ cy i₂) (ht i₂) (ex₂ i₁ i₂)
    have c₁ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom
      (F := modulePullbackPseudofunctor)
      (lineBundleComparisonIso t (cx i₁) (φ i₁ ≫ cy i₁) (ht i₁)).hom
      (ex₁ i₁ i₂).totalMap _ _ k yy yy rfl rfl hy₁ hy₁
    have c₂ := Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom
      (F := modulePullbackPseudofunctor)
      (lineBundleComparisonIso t (cx i₂) (φ i₂ ≫ cy i₂) (ht i₂)).hom
      (ex₂ i₁ i₂).totalMap _ _ k yy yy rfl rfl hy₂ hy₂
    rw [n₁] at c₁
    rw [n₂] at c₂
    exact c₁.symm.trans ((pullHom_lineBundleComparisonIso_congr t (hex i₁ i₂) (hψ i₁ i₂) _ _ k
      yy hy₁ hy₂).trans c₂)
  have hΘinv : ∀ {Y : Scheme.{u}} (yy : Y ⟶ x.total) (i₁ i₂ : I) (d₁ : Y ⟶ (ax i₁).total)
      (d₂ : Y ⟶ (ax i₂).total) (hd₁ : d₁ ≫ (cx i₁).totalMap = yy)
      (hd₂ : d₂ ≫ (cx i₂).totalMap = yy),
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulePullbackPseudofunctor)
          (lineBundleComparisonIso t (cx i₁) (φ i₁ ≫ cy i₁) (ht i₁)).inv d₁ yy yy hd₁ hd₁ =
        Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := modulePullbackPseudofunctor)
          (lineBundleComparisonIso t (cx i₂) (φ i₂ ≫ cy i₂) (ht i₂)).inv d₂ yy yy hd₂ hd₂ := by
    intro Y yy i₁ i₂ d₁ d₂ hd₁ hd₂
    have hinv₁ := pullHom_inv_comp_hom (lineBundleComparisonIso t (cx i₁) (φ i₁ ≫ cy i₁) (ht i₁))
      d₁ yy hd₁
    have hinv₂ := pullHom_hom_comp_inv (lineBundleComparisonIso t (cx i₂) (φ i₂ ≫ cy i₂) (ht i₂))
      d₂ yy hd₂
    rw [← hΘ yy i₁ i₂ d₁ d₂ hd₁ hd₂] at hinv₂
    exact (Category.comp_id _).symm.trans
      (by rw [← hinv₂, ← Category.assoc, hinv₁, Category.id_comp])
  obtain ⟨τ, hτ, -⟩ := existsUnique_map_eq_of_mem_fpqcTopology (fun i ↦ (cx i).totalMap)
    ((Scheme.Modules.pullback t).obj y.lineBundle) x.lineBundle hcx hM hN
    (fun i ↦ (lineBundleComparisonIso t (cx i) (φ i ≫ cy i) (ht i)).hom) hΘ
  obtain ⟨τ', hτ', -⟩ := existsUnique_map_eq_of_mem_fpqcTopology (fun i ↦ (cx i).totalMap)
    x.lineBundle ((Scheme.Modules.pullback t).obj y.lineBundle) hcx hN hM
    (fun i ↦ (lineBundleComparisonIso t (cx i) (φ i ≫ cy i) (ht i)).inv) hΘinv
  have h₁ : τ ≫ τ' = 𝟙 _ := eq_of_map_eq_of_mem_fpqcTopology _ _ _ hcx hM hM _ _ fun i ↦
    ((Functor.map_comp _ τ τ').trans (congrArg₂ (· ≫ ·) (hτ i) (hτ' i))).trans
      ((lineBundleComparisonIso t (cx i) (φ i ≫ cy i) (ht i)).hom_inv_id.trans
        (CategoryTheory.Functor.map_id _ _).symm)
  have h₂ : τ' ≫ τ = 𝟙 _ := eq_of_map_eq_of_mem_fpqcTopology _ _ _ hcx hN hN _ _ fun i ↦
    ((Functor.map_comp _ τ' τ).trans (congrArg₂ (· ≫ ·) (hτ' i) (hτ i))).trans
      ((lineBundleComparisonIso t (cx i) (φ i ≫ cy i) (ht i)).inv_hom_id.trans
        (CategoryTheory.Functor.map_id _ _).symm)
  let g : x ⟶ y := ⟨eqToHom hy.symm, t, hcart, ⟨τ, τ', h₁, h₂⟩⟩
  refine ⟨g, ⟨rfl, fun i ↦ ?_⟩, ?_⟩
  · refine (comp_eq_iff (cx i) g (φ i ≫ cy i) ?_ (ht i)).2 (hτ i)
    show (cx i).baseMap ≫ eqToHom hy.symm = (φ i).baseMap ≫ (cy i).baseMap
    exact (hb i).symm
  · rintro g' ⟨hg'b, hg'⟩
    have ht' : g'.totalMap = t := eq_of_comp_eq_of_mem_fpqcTopology _ hcx _ _ fun i ↦ by
      rw [ht i, ← comp_totalMap, hg' i]
    obtain ⟨b', t', c', L'⟩ := g'
    change t' = t at ht'
    change b' = eqToHom hy.symm at hg'b
    subst ht' hg'b
    have hL : L' = ⟨τ, τ', h₁, h₂⟩ := by
      refine Iso.ext (eq_of_map_eq_of_mem_fpqcTopology _ _ _ hcx hM hN _ _ fun i ↦ ?_)
      exact ((comp_eq_iff (cx i) ⟨_, _, c', L'⟩ (φ i ≫ cy i)
        (by change (cx i).baseMap ≫ eqToHom hy.symm = _; exact (hb i).symm) (ht i)).1
          (hg' i)).trans (hτ i).symm
    subst hL
    rfl

end PolarizedFamily

end Polarized

/-! ### The `Isom` condition of Stacks 02ZI for polarized families -/

section IsomSheaf

/-- A covering family stays covering when its members and its target are replaced by equal
objects, along `eqToHom`. -/
theorem _root_.CategoryTheory.GrothendieckTopology.ofArrows_eqToHom_mem {C : Type*}
    [Category C] (J : GrothendieckTopology C) {U U' : C} {I : Type*} {V A : I → C}
    {f : ∀ i, V i ⟶ U} (hf : Sieve.ofArrows V f ∈ J U) (hA : ∀ i, A i = V i) (hU : U = U') :
    Sieve.ofArrows A (fun i ↦ eqToHom (hA i) ≫ f i ≫ eqToHom hU) ∈ J U' := by
  subst hU
  refine J.superset_covering ?_ hf
  rintro Z g ⟨Y, h, _, ⟨i⟩, rfl⟩
  exact ⟨A i, h ≫ eqToHom (hA i).symm, _, ⟨i⟩, by simp⟩

variable {B : BigFppfSite.{u}}

/-- The base map of a morphism of polarized families lying over a morphism of the site. -/
theorem PolarizedFamily.baseMap_eq_of_isHomLift {a b : PolarizedFamily B} (f : a.base ⟶ b.base)
    (φ : a ⟶ b) [h : (polarizedProjection B).IsHomLift f φ] : φ.baseMap = f :=
  (@CategoryTheory.IsHomLift.eq_of_isHomLift _ _ _ _ (polarizedProjection B) a b f φ h).symm

/-- A restriction of a polarized family lies over the base morphism it is taken along. -/
private theorem restriction_hom_baseMap {x : PolarizedFamily B} {U V : B.Schemes} {f : V ⟶ U}
    (hx : x.base = U) (r : Functor.Restriction (polarizedProjection B) f x hx)
    (hr : r.pt.base = V) : r.hom.baseMap = eqToHom hr ≫ f ≫ eqToHom hx.symm := by
  have : (polarizedProjection B).IsHomLift (eqToHom hr ≫ f ≫ eqToHom hx.symm) r.hom :=
    r.isHomLift
  exact PolarizedFamily.baseMap_eq_of_isHomLift _ _

/-- The canonical comparison of two restrictions of a polarized family lies over the base
morphism it is taken along. -/
private theorem baseMap_compTo [(polarizedProjection B).IsFibered] {x : PolarizedFamily B}
    {U V W : B.Schemes} {f : V ⟶ U} {m : W ⟶ U} (g : W ⟶ V) (hm : m = g ≫ f)
    (hx : x.base = U) (xr : Functor.Restriction (polarizedProjection B) f x hx)
    (xrW : Functor.Restriction (polarizedProjection B) m x hx) (hW : xrW.pt.base = W)
    (hV : xr.pt.base = V) :
    (Functor.Restriction.compTo _ g f hm xr xrW).baseMap = eqToHom hW ≫ g ≫ eqToHom hV.symm := by
  have := Functor.Restriction.isHomLift_compTo g f hm xr xrW
  have : (polarizedProjection B).IsHomLift (eqToHom hW ≫ g ≫ eqToHom hV.symm)
      (Functor.Restriction.compTo _ g f hm xr xrW) := by simpa using this
  exact PolarizedFamily.baseMap_eq_of_isHomLift _ _

/-- The total spaces of a cartesian square of morphisms of polarized families form a cartesian
square as soon as the bases do. -/
private theorem isPullback_totalMap_of_isPullback_baseMap {W Xi Xj X : PolarizedFamily B}
    (e₁ : W ⟶ Xi) (e₂ : W ⟶ Xj) (ci : Xi ⟶ X) (cj : Xj ⟶ X) (he : e₁ ≫ ci = e₂ ≫ cj)
    (hbase : IsPullback (B.inclusion.map e₁.baseMap) (B.inclusion.map e₂.baseMap)
      (B.inclusion.map ci.baseMap) (B.inclusion.map cj.baseMap)) :
    IsPullback e₁.totalMap e₂.totalMap ci.totalMap cj.totalMap :=
  isPullback_of_isPullback_base e₁.cartesian e₂.cartesian.toCommSq ci.cartesian.toCommSq
    cj.cartesian hbase
    (by rw [← PolarizedFamily.comp_totalMap, ← PolarizedFamily.comp_totalMap, he])

/-- The maps of total spaces of the restrictions of a polarized family along a covering of the
base generate an fpqc covering sieve. -/
private theorem ofArrows_totalMap_mem_fpqcTopology {x : PolarizedFamily B} {U : B.Schemes}
    (hx : x.base = U) {I : Type w} (V : I → B.Schemes) (f : ∀ i, V i ⟶ U)
    (hf : Sieve.ofArrows V f ∈ B.topology U)
    (xr : ∀ i, Functor.Restriction (polarizedProjection B) (f i) x hx) :
    Sieve.ofArrows (fun i ↦ (xr i).pt.total) (fun i ↦ (xr i).hom.totalMap) ∈
      Scheme.fpqcTopology x.total := by
  have hbx : Sieve.ofArrows (fun i ↦ (xr i).pt.base) (fun i ↦ (xr i).hom.baseMap) ∈
      B.topology x.base := by
    have hxp : ∀ i, (xr i).pt.base = V i := fun i ↦ (xr i).hpt
    convert B.topology.ofArrows_eqToHom_mem hf hxp hx.symm using 2
    exact funext fun i ↦ restriction_hom_baseMap hx (xr i) (hxp i)
  exact mem_fpqcTopology_of_isPullback B (fun i ↦ (xr i).hom.baseMap) hbx x.toBase
    (fun i ↦ (xr i).hom.totalMap) (fun i ↦ (xr i).pt.toBase) fun i ↦ (xr i).hom.cartesian

/-- **The `Isom` condition of Stacks 02ZI for polarized families** (Stacks 0D40, the descent of
morphisms). For two polarized families over `U` and a covering family of
`U`, a family of isomorphisms between their restrictions agreeing on the double overlaps glues
to a unique isomorphism over `U`. -/
theorem polarizedProjection_isomIsSheafFor {U : B.Schemes} (x y : PolarizedFamily B)
    (hx : (polarizedProjection B).obj x = U) (hy : (polarizedProjection B).obj y = U)
    {I : Type w} (V : I → B.Schemes) (f : ∀ i, V i ⟶ U) (hf : Sieve.ofArrows V f ∈ B.topology U)
    (Vij : I → I → B.Schemes) (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
    (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
    (xr : ∀ i, Functor.Restriction (polarizedProjection B) (f i) x hx)
    (yr : ∀ i, Functor.Restriction (polarizedProjection B) (f i) y hy)
    (xrij : ∀ i j, Functor.Restriction (polarizedProjection B) (pr₁ i j ≫ f i) x hx)
    (yrij : ∀ i j, Functor.Restriction (polarizedProjection B) (pr₁ i j ≫ f i) y hy) :
    Functor.IsomIsSheafFor (polarizedProjection B) x y hx hy V f Vij pr₁ pr₂ hVij xr yr xrij
      yrij := by
  intro φ hφfib hφiso hcompat
  choose γ hγfib hγ₁ hγ₂ using hcompat
  have hp := polarizedProjection_isFiberedInGroupoids_unconditional (B := B)
  have := hp.isFibered
  have : ∀ i j, IsIso (γ i j) := fun i j ↦ Functor.isIso_of_fibreHom hp (hγfib i j)
  have hx' : x.base = U := hx
  have hy' : y.base = x.base := hy.trans hx.symm
  have hyU : y.base = U := hy
  have hxp : ∀ i, (xr i).pt.base = V i := fun i ↦ (xr i).hpt
  have hyp : ∀ i, (yr i).pt.base = V i := fun i ↦ (yr i).hpt
  have hxpij : ∀ i j, (xrij i j).pt.base = Vij i j := fun i j ↦ (xrij i j).hpt
  have hypij : ∀ i j, (yrij i j).pt.base = Vij i j := fun i j ↦ (yrij i j).hpt
  -- the four families of comparison maps and their base maps
  obtain ⟨ex₁, hex₁⟩ : ∃ e : ∀ i j, (xrij i j).pt ⟶ (xr i).pt,
      e = fun i j ↦ Functor.Restriction.compTo _ (pr₁ i j) (f i) rfl (xr i) (xrij i j) :=
    ⟨_, rfl⟩
  obtain ⟨ex₂, hex₂⟩ : ∃ e : ∀ i j, (xrij i j).pt ⟶ (xr j).pt,
      e = fun i j ↦ Functor.Restriction.compTo _ (pr₂ i j) (f j) (hVij i j).w (xr j)
        (xrij i j) := ⟨_, rfl⟩
  obtain ⟨ey₁, hey₁⟩ : ∃ e : ∀ i j, (yrij i j).pt ⟶ (yr i).pt,
      e = fun i j ↦ Functor.Restriction.compTo _ (pr₁ i j) (f i) rfl (yr i) (yrij i j) :=
    ⟨_, rfl⟩
  obtain ⟨ey₂, hey₂⟩ : ∃ e : ∀ i j, (yrij i j).pt ⟶ (yr j).pt,
      e = fun i j ↦ Functor.Restriction.compTo _ (pr₂ i j) (f j) (hVij i j).w (yr j)
        (yrij i j) := ⟨_, rfl⟩
  have bx := fun i ↦ restriction_hom_baseMap hx' (xr i) (hxp i)
  have by' := fun i ↦ restriction_hom_baseMap hyU (yr i) (hyp i)
  have bφ : ∀ i, (φ i).baseMap = eqToHom (hxp i) ≫ eqToHom (hyp i).symm := fun i ↦ by
    have : (polarizedProjection B).IsHomLift (eqToHom (hxp i) ≫ eqToHom (hyp i).symm) (φ i) :=
      hφfib i
    exact PolarizedFamily.baseMap_eq_of_isHomLift _ _
  have bex₁ : ∀ i j, (ex₁ i j).baseMap = eqToHom (hxpij i j) ≫ pr₁ i j ≫ eqToHom (hxp i).symm :=
    fun i j ↦ by subst hex₁; exact baseMap_compTo _ _ _ _ _ (hxpij i j) (hxp i)
  have bex₂ : ∀ i j, (ex₂ i j).baseMap = eqToHom (hxpij i j) ≫ pr₂ i j ≫ eqToHom (hxp j).symm :=
    fun i j ↦ by subst hex₂; exact baseMap_compTo _ _ _ _ _ (hxpij i j) (hxp j)
  have bey₁ : ∀ i j, (ey₁ i j).baseMap = eqToHom (hypij i j) ≫ pr₁ i j ≫ eqToHom (hyp i).symm :=
    fun i j ↦ by subst hey₁; exact baseMap_compTo _ _ _ _ _ (hypij i j) (hyp i)
  have bey₂ : ∀ i j, (ey₂ i j).baseMap = eqToHom (hypij i j) ≫ pr₂ i j ≫ eqToHom (hyp j).symm :=
    fun i j ↦ by subst hey₂; exact baseMap_compTo _ _ _ _ _ (hypij i j) (hyp j)
  -- the comparison maps factor the restrictions
  have hcx₁ : ∀ i j, ex₁ i j ≫ (xr i).hom = (xrij i j).hom := fun i j ↦ by
    subst hex₁; exact Functor.Restriction.compTo_hom _ _ _ _ _ _
  have hcx₂ : ∀ i j, ex₂ i j ≫ (xr j).hom = (xrij i j).hom := fun i j ↦ by
    subst hex₂; exact Functor.Restriction.compTo_hom _ _ _ _ _ _
  have hcy₁ : ∀ i j, ey₁ i j ≫ (yr i).hom = (yrij i j).hom := fun i j ↦ by
    subst hey₁; exact Functor.Restriction.compTo_hom _ _ _ _ _ _
  have hcy₂ : ∀ i j, ey₂ i j ≫ (yr j).hom = (yrij i j).hom := fun i j ↦ by
    subst hey₂; exact Functor.Restriction.compTo_hom _ _ _ _ _ _
  -- the coverings of the total spaces
  have hcovx := ofArrows_totalMap_mem_fpqcTopology hx' V f hf xr
  have hcovy := ofArrows_totalMap_mem_fpqcTopology hyU V f hf yr
  have hpx : ∀ i j, IsPullback (ex₁ i j).totalMap (ex₂ i j).totalMap (xr i).hom.totalMap
      (xr j).hom.totalMap := fun i j ↦
    isPullback_totalMap_of_isPullback_baseMap _ _ _ _
      (by rw [hcx₁, hcx₂]) (by
        rw [bex₁, bex₂, bx, bx]
        exact ((hVij i j).eqToHom_conj (hxpij i j) (hxp i).symm (hxp j).symm hx'.symm).map
          B.inclusion)
  have hpy : ∀ i j, IsPullback (ey₁ i j).totalMap (ey₂ i j).totalMap (yr i).hom.totalMap
      (yr j).hom.totalMap := fun i j ↦
    isPullback_totalMap_of_isPullback_baseMap _ _ _ _
      (by rw [hcy₁, hcy₂]) (by
        rw [bey₁, bey₂, by', by']
        exact ((hVij i j).eqToHom_conj (hypij i j) (hyp i).symm (hyp j).symm hyU.symm).map
          B.inclusion)
  have hγ₁' : ∀ i j, γ i j ≫ ey₁ i j = ex₁ i j ≫ φ i := fun i j ↦ by
    subst hex₁ hey₁; exact hγ₁ i j
  have hγ₂' : ∀ i j, γ i j ≫ ey₂ i j = ex₂ i j ≫ φ j := fun i j ↦ by
    subst hex₂ hey₂; exact hγ₂ i j
  have hb : ∀ i, (φ i).baseMap ≫ (yr i).hom.baseMap = (xr i).hom.baseMap ≫ eqToHom hy'.symm :=
    fun i ↦ by
      rw [bφ, by', bx]
      simp
  have := hφiso
  obtain ⟨g, ⟨hgb, hg⟩, hg_uniq⟩ := PolarizedFamily.existsUnique_glue hy' (fun i ↦ (xr i).hom)
    (fun i ↦ (yr i).hom) φ hb hcovx hcovy ex₁ ex₂ (fun i j ↦ (hcx₁ i j).trans (hcx₂ i j).symm)
    hpx ey₁ ey₂ (fun i j ↦ (hcy₁ i j).trans (hcy₂ i j).symm) hpy γ hγ₁' hγ₂'
  have hfib : ∀ g' : x ⟶ y, g'.baseMap = eqToHom hy'.symm →
      Functor.FibreHom (polarizedProjection B) x y hx hy g' := fun g' h' ↦
    (Functor.fibreHom_iff hx hy g').2 (CategoryTheory.IsHomLift.of_fac' _ _ g' hx hy (by
      show g'.baseMap = _
      rw [h']
      simp only [Category.id_comp, eqToHom_trans]
      rfl))
  refine ⟨g, ⟨hfib g hgb, Functor.isIso_of_fibreHom hp (hfib g hgb), hg⟩, ?_⟩
  rintro g' ⟨hfib', -, hcomp⟩
  refine hg_uniq g' ⟨?_, hcomp⟩
  have h₀ := (Functor.fibreHom_iff hx hy g').1 hfib'
  refine (CategoryTheory.IsHomLift.fac' (polarizedProjection B) (𝟙 U) g').trans ?_
  simp only [Category.id_comp, eqToHom_trans]
  rfl

end IsomSheaf

end AlgebraicGeometry

end

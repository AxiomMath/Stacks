module

public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactModuleSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.ShriekConstantFree
public import StacksFrontier.CategoryTheory.Sites.Continuous.PullbackOfSheafifiedYoneda
public import StacksFrontier.CategoryTheory.Sites.Localization.FreeModuleSheafCompatibility
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local sections of free module sheaves on sheafified representables

Let `(C, J)` be a site and `R` a commutative ring. For an object `U` of `C` write `Λ_U` for the
free module sheaf on the sheafified representable `h_U^#`, that is
`CategoryTheory.Sheaf.composeAndSheafify J (ModuleCat.free R)` applied to
`CategoryTheory.Sheaf.sheafifiedYoneda J` at `U`; it is the extension by zero `j_{U!} R_U` of the
constant sheaf (`CategoryTheory.Sheaf.sheafPullbackConstantSheafIsoComposeAndSheafifyFree`), and a
morphism out of it is a section over `U` (`CategoryTheory.Sheaf.freeSectionEquiv`).

This file proves that every section of `Λ_U` is, locally, an `R`-linear combination of the
*elementary* sections: the restrictions along morphisms `φ : V ⟶ U` of the tautological section
over `U`. Read through `CategoryTheory.Sheaf.freeSectionEquiv`, every morphism `Λ_V ⟶ Λ_U` is,
after restriction to the members of a covering of `V`, a linear combination of the morphisms
`Λ_φ` induced by morphisms of the site. This is what makes a morphism between finite direct sums
of such sheaves a finite amount of geometric data, which can be moved along a limit of sites.

## Main definitions

* `CategoryTheory.Sheaf.smulEnd` — multiplication by a scalar `r : R` on a sheaf of
  `R`-modules.

## Main results

* `CategoryTheory.Sheaf.freeSectionEquiv_eq_app` and
  `CategoryTheory.Sheaf.freeSectionEquiv_map_comp` — the bijection
  `CategoryTheory.Sheaf.freeSectionEquiv` is evaluation at the tautological section, and is natural
  in the object of the site.
* `CategoryTheory.Sheaf.freeSectionEquiv_id` — the tautological section is the image under
  sheafification of the generator `[id_U]`.
* `CategoryTheory.Sheaf.elementarySieve_mem` — **sections of `Λ_U` are locally
  elementary.**
* `CategoryTheory.Sheaf.freeModuleSheaf_hom_locally` — **morphisms `Λ_V ⟶ Λ_U` are locally linear
  combinations of the `Λ_φ`.**
* `CategoryTheory.Sheaf.epi_sigmaDesc_freeModuleSheaf_map` — a family of morphisms generating a
  covering sieve induces an epimorphism of free module sheaves.
* `CategoryTheory.Sheaf.map_smulEnd_of_adjunction` — a left adjoint whose right adjoint commutes
  with multiplication by scalars commutes with it too.

## References

* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 093C](https://stacks.math.columbia.edu/tag/093C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace CategoryTheory.Sheaf

section Smul

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) {R : Type*} [CommRing R]

/-- Multiplication by the scalar `r` on a sheaf of `R`-modules. -/
def smulEnd (r : R) (F : Sheaf J (ModuleCat.{w} R)) : F ⟶ F :=
  Sheaf.Hom.mk (r • 𝟙 F.obj)

/-- The component of `smulEnd J r F` at `U` sends a section `x` to `r • x`. -/
@[simp]
lemma smulEnd_hom_app_apply (r : R) (F : Sheaf J (ModuleCat.{w} R)) (U : Cᵒᵖ)
    (x : F.obj.obj U) : (smulEnd J r F).hom.app U x = r • x :=
  rfl

/-- Multiplication by a scalar commutes with every morphism of sheaves of modules. -/
@[reassoc]
lemma comp_smulEnd (r : R) {F G : Sheaf J (ModuleCat.{w} R)} (h : F ⟶ G) :
    h ≫ smulEnd J r G = smulEnd J r F ≫ h := by
  ext U x
  show r • (h.hom.app U) x = (h.hom.app U) (r • x)
  exact ((h.hom.app U).hom.map_smul r x).symm

/-- **A left adjoint commutes with multiplication by scalars** as soon as its right adjoint does.
-/
lemma map_smulEnd_of_adjunction {D : Type*} [Category* D] (K : GrothendieckTopology D)
    {L : Sheaf J (ModuleCat.{w} R) ⥤ Sheaf K (ModuleCat.{w} R)}
    {G : Sheaf K (ModuleCat.{w} R) ⥤ Sheaf J (ModuleCat.{w} R)} (adj : L ⊣ G)
    (hG : ∀ (r : R) (F : Sheaf K (ModuleCat.{w} R)), G.map (smulEnd K r F) = smulEnd J r (G.obj F))
    (r : R) (F : Sheaf J (ModuleCat.{w} R)) :
    L.map (smulEnd J r F) = smulEnd K r (L.obj F) := by
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, hG, ← Functor.comp_map,
    ← adj.unit.naturality]
  exact (comp_smulEnd J r (adj.unit.app F)).symm

end Smul

section Free

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type max u v) [CommRing R]
  [HasWeakSheafify J (ModuleCat.{max u v} R)]

/-- The free module sheaf `Λ_U` on the sheafified representable `h_U^#`, as a functor of `U`. -/
@[sga "4 II 6.8" "special case"]
abbrev freeModuleSheaf : C ⥤ Sheaf J (ModuleCat.{max u v} R) :=
  sheafifiedYoneda J ⋙ composeAndSheafify J (ModuleCat.free R)

/-- The tautological section of `Λ_U` over `U`: the section that the identity of `Λ_U` is under
`CategoryTheory.Sheaf.freeSectionEquiv`. -/
abbrev freeTautologicalSection (U : C) :
    (forget (ModuleCat.{max u v} R)).obj (((freeModuleSheaf J R).obj U).obj.obj (op U)) :=
  freeSectionEquiv J R U _ (𝟙 _)

/-- `CategoryTheory.Sheaf.freeSectionEquiv` is evaluation at the tautological section. -/
lemma freeSectionEquiv_eq_app (U : C) (F : Sheaf J (ModuleCat.{max u v} R))
    (h : (freeModuleSheaf J R).obj U ⟶ F) :
    freeSectionEquiv J R U F h = h.hom.app (op U) (freeTautologicalSection J R U) := by
  conv_lhs => rw [← Category.id_comp h]
  show sectionEquiv J ((adjunction J (ModuleCat.adj R)).homEquiv _ F (𝟙 _ ≫ h)) = _
  rw [(adjunction J (ModuleCat.adj R)).homEquiv_naturality_right, sectionEquiv_comp]
  rfl

/-- `CategoryTheory.Sheaf.freeSectionEquiv` is natural in the object of the site: precomposing with
`Λ_g` restricts the section along `g`. -/
lemma freeSectionEquiv_map_comp {U V : C} (g : V ⟶ U) (F : Sheaf J (ModuleCat.{max u v} R))
    (h : (freeModuleSheaf J R).obj U ⟶ F) :
    freeSectionEquiv J R V F ((freeModuleSheaf J R).map g ≫ h) =
      F.obj.map g.op (freeSectionEquiv J R U F h) := by
  show sectionEquiv J ((adjunction J (ModuleCat.adj R)).homEquiv _ F
    ((composeAndSheafify J (ModuleCat.free R)).map ((sheafifiedYoneda J).map g) ≫ h)) = _
  rw [(adjunction J (ModuleCat.adj R)).homEquiv_naturality_left, sectionEquiv_map_comp]
  rfl

/-- The tautological section of `Λ_U` is the image under sheafification of the generator
`[t_U]`, where `t_U` is the tautological section of `h_U^#`. -/
lemma freeSectionEquiv_id (U : C) :
    freeTautologicalSection J R U =
      (toSheafify J (((sheafifiedYoneda J).obj U).obj ⋙ ModuleCat.free R)).app (op U)
        (ModuleCat.freeMk (tautologicalSection J U)) := by
  show sectionEquiv J ((adjunction J (ModuleCat.adj R)).homEquiv _ _ (𝟙 _)) = _
  rw [Adjunction.homEquiv_id, ← Category.id_comp ((adjunction J (ModuleCat.adj R)).unit.app _),
    sectionEquiv_comp, adjunction_unit_app_hom]
  rfl

/-- The sieve of the morphisms `g : W ⟶ V` along which a section `x` of `Λ_U` over `V` restricts
to an `R`-linear combination of the *elementary* sections, the restrictions of the tautological
section of `Λ_U` along morphisms `W ⟶ U`. -/
def elementarySieve (U : C) {V : C}
    (x : (forget (ModuleCat.{max u v} R)).obj (((freeModuleSheaf J R).obj U).obj.obj (op V))) :
    Sieve V where
  arrows W g := ∃ (n : ℕ) (φ : Fin n → (W ⟶ U)) (c : Fin n → R),
    ((freeModuleSheaf J R).obj U).obj.map g.op x =
      ∑ k, c k • ((freeModuleSheaf J R).obj U).obj.map (φ k).op (freeTautologicalSection J R U)
  downward_closed := by
    rintro W W' g ⟨n, φ, c, h⟩ g'
    refine ⟨n, fun k ↦ g' ≫ φ k, c, ?_⟩
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, h, map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [map_smul, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]

variable {J R} in
/-- The elementary sieve of the restriction of `x` along `g` is contained in the pullback along `g`
of the elementary sieve of `x`. -/
lemma elementarySieve_le_pullback (U : C) {V W : C} (g : W ⟶ V)
    (x : (forget (ModuleCat.{max u v} R)).obj (((freeModuleSheaf J R).obj U).obj.obj (op V))) :
    elementarySieve J R U (((freeModuleSheaf J R).obj U).obj.map g.op x) ≤
      (elementarySieve J R U x).pullback g := by
  rintro W' g' ⟨n, φ, c, h⟩
  refine ⟨n, φ, c, ?_⟩
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, h]

variable {J R} in
/-- The elementary sieve of the zero section is the maximal sieve. -/
lemma elementarySieve_zero (U : C) {V : C} :
    elementarySieve J R U (0 : (forget (ModuleCat.{max u v} R)).obj
      (((freeModuleSheaf J R).obj U).obj.obj (op V))) = ⊤ := by
  ext W g
  simp only [Sieve.top_apply, iff_true]
  exact ⟨0, Fin.elim0, Fin.elim0, by rw [map_zero, Finset.univ_eq_empty, Finset.sum_empty]⟩

variable {J R} in
/-- The elementary sieve of `x + y` contains the intersection of the elementary sieves of `x` and
`y`. -/
lemma elementarySieve_add (U : C) {V : C}
    (x y : (forget (ModuleCat.{max u v} R)).obj (((freeModuleSheaf J R).obj U).obj.obj (op V))) :
    elementarySieve J R U x ⊓ elementarySieve J R U y ≤ elementarySieve J R U (x + y) := by
  rintro W g ⟨⟨n, φ, c, hx⟩, ⟨m, ψ, d, hy⟩⟩
  refine ⟨n + m, Fin.append φ ψ, Fin.append c d, ?_⟩
  rw [map_add, hx, hy, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

variable {J R} in
/-- The elementary sieve of `r • x` contains the elementary sieve of `x`. -/
lemma elementarySieve_smul (U : C) {V : C} (r : R)
    (x : (forget (ModuleCat.{max u v} R)).obj (((freeModuleSheaf J R).obj U).obj.obj (op V))) :
    elementarySieve J R U x ≤ elementarySieve J R U (r • x) := by
  rintro W g ⟨n, φ, c, hx⟩
  refine ⟨n, φ, fun k ↦ r * c k, ?_⟩
  rw [map_smul, hx, Finset.smul_sum]
  simp only [smul_smul]

/-- **Sections of `Λ_U` are locally elementary.** Every section of `Λ_U` over `V` restricts, along
the members of a covering sieve of `V`, to an `R`-linear combination of restrictions of the
tautological section of `Λ_U`. -/
theorem elementarySieve_mem (U : C) {V : C}
    (x : (forget (ModuleCat.{max u v} R)).obj (((freeModuleSheaf J R).obj U).obj.obj (op V))) :
    elementarySieve J R U x ∈ J V := by
  have := preservesSheafification_forget_moduleCat.{max u v, v, u} J R
  let τ := toSheafify J (((sheafifiedYoneda J).obj U).obj ⋙ ModuleCat.free R)
  have hgen : ∀ {W : C} (s : ((sheafifiedYoneda J).obj U).obj.obj (op W)),
      elementarySieve J R U (τ.app (op W) (ModuleCat.freeMk s)) ∈ J W := by
    intro W s
    refine J.superset_covering ?_
      (Presheaf.imageSieve_mem J (toSheafify J (uliftYoneda.{u}.obj U)) (U := op W) s)
    rintro W' g' ⟨⟨ψ⟩, hψ⟩
    refine ⟨1, fun _ ↦ ψ, fun _ ↦ 1, ?_⟩
    rw [Fin.sum_univ_one, one_smul, freeSectionEquiv_id]
    have hnat : ∀ {A B : C} (f : A ⟶ B) (t : (((sheafifiedYoneda J).obj U).obj ⋙
        ModuleCat.free R).obj (op B)), ((freeModuleSheaf J R).obj U).obj.map f.op (τ.app (op B) t) =
        τ.app (op A) ((((sheafifiedYoneda J).obj U).obj ⋙ ModuleCat.free R).map f.op t) :=
      fun f t ↦ (NatTrans.naturality_apply τ f.op t).symm
    rw [hnat, hnat]
    congr 1
    show (ModuleCat.free R).map _ (ModuleCat.freeMk s) =
      (ModuleCat.free R).map _ (ModuleCat.freeMk (tautologicalSection J U))
    rw [ModuleCat.free_map_apply, ModuleCat.free_map_apply, map_op_tautologicalSection,
      sectionEquiv_sheafifiedYoneda_map]
    exact congrArg ModuleCat.freeMk hψ.symm
  have hpre : ∀ {W : C} (t : (((sheafifiedYoneda J).obj U).obj ⋙ ModuleCat.free R).obj (op W)),
      elementarySieve J R U (τ.app (op W) t) ∈ J W := by
    intro W t
    induction t using Finsupp.induction_linear with
    | zero =>
      have e : τ.app (op W) (0 : ((sheafifiedYoneda J).obj U).obj.obj (op W) →₀ R) = 0 :=
        map_zero (τ.app (op W)).hom
      rw [e, elementarySieve_zero]
      exact J.top_mem W
    | add t₁ t₂ h₁ h₂ =>
      have e : τ.app (op W) (t₁ + t₂) = τ.app (op W) t₁ + τ.app (op W) t₂ := map_add _ _ _
      rw [e]
      exact J.superset_covering (elementarySieve_add U _ _) (J.intersection_covering h₁ h₂)
    | single s r =>
      have e : τ.app (op W) (Finsupp.single s r) = r • τ.app (op W) (ModuleCat.freeMk s) := by
        rw [← map_smul]
        congr 1
        exact (Finsupp.smul_single_one s r).symm
      rw [e]
      exact J.superset_covering (elementarySieve_smul U r _) (hgen s)
  refine J.transitive (Presheaf.imageSieve_mem J τ (U := op V) x) _ ?_
  rintro W g ⟨t, ht⟩
  exact J.superset_covering (elementarySieve_le_pullback U g x) (ht ▸ hpre t)

/-- **Morphisms `Λ_V ⟶ Λ_U` are locally linear combinations of the `Λ_φ`.** For a morphism
`s : Λ_V ⟶ Λ_U` there is a covering sieve of `V` along each member `g : W ⟶ V` of which `Λ_g ≫ s`
is a finite sum of morphisms `Λ_φ ≫ r` for morphisms `φ : W ⟶ U` of the site and scalars `r`. -/
theorem freeModuleSheaf_hom_locally {U V : C}
    (s : (freeModuleSheaf J R).obj V ⟶ (freeModuleSheaf J R).obj U) :
    ∃ S ∈ J V, ∀ ⦃W : C⦄ (g : W ⟶ V), S g → ∃ (n : ℕ) (φ : Fin n → (W ⟶ U)) (c : Fin n → R),
      (freeModuleSheaf J R).map g ≫ s =
        ∑ k, (freeModuleSheaf J R).map (φ k) ≫ smulEnd J (c k) _ := by
  refine ⟨_, elementarySieve_mem J R U (freeSectionEquiv J R V _ s), fun W g ⟨n, φ, c, h⟩ ↦
    ⟨n, φ, c, (freeSectionEquiv J R W _).injective ?_⟩⟩
  rw [freeSectionEquiv_map_comp, h, freeSectionEquiv_eq_app]
  let ev : ((freeModuleSheaf J R).obj W ⟶ (freeModuleSheaf J R).obj U) →+
      (forget (ModuleCat.{max u v} R)).obj (((freeModuleSheaf J R).obj U).obj.obj (op W)) :=
    { toFun h := h.hom.app (op W) (freeTautologicalSection J R W)
      map_zero' := rfl
      map_add' _ _ := rfl }
  show _ = ev _
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  show _ = (smulEnd J (c k) _).hom.app (op W)
    (((freeModuleSheaf J R).map (φ k)).hom.app (op W) (freeTautologicalSection J R W))
  rw [smulEnd_hom_app_apply, ← freeSectionEquiv_eq_app, ← Category.comp_id
    ((freeModuleSheaf J R).map (φ k)), freeSectionEquiv_map_comp]
  rfl

/-- **A covering family induces an epimorphism of free module sheaves.** If the morphisms
`g i : W i ⟶ V` generate a covering sieve of `V`, then `∐ Λ_{W i} ⟶ Λ_V` is an epimorphism. -/
theorem epi_sigmaDesc_freeModuleSheaf_map {ι : Type*} {V : C} {W : ι → C} (g : ∀ i, W i ⟶ V)
    (hg : Sieve.ofArrows W g ∈ J V)
    [HasCoproduct (fun i ↦ (freeModuleSheaf J R).obj (W i))] :
    Epi (Limits.Sigma.desc fun i ↦ (freeModuleSheaf J R).map (g i)) := by
  refine ⟨fun {G} a b hab ↦ (freeSectionEquiv J R V G).injective ?_⟩
  have hi : ∀ i, (freeModuleSheaf J R).map (g i) ≫ a = (freeModuleSheaf J R).map (g i) ≫ b :=
    fun i ↦ by simpa only [Limits.Sigma.ι_desc_assoc] using Limits.Sigma.ι _ i ≫= hab
  let G' := (sheafCompose J (forget (ModuleCat.{max u v} R))).obj G
  refine ((isSheaf_iff_isSheaf_of_type J G'.obj).1 G'.cond _ hg).isSeparatedFor.ext ?_
  rintro Y f ⟨Y', h, g', ⟨i⟩, rfl⟩
  show G.obj.map (h ≫ g i).op _ = G.obj.map (h ≫ g i).op _
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    ← freeSectionEquiv_map_comp, ← freeSectionEquiv_map_comp, hi i, freeSectionEquiv_map_comp,
    freeSectionEquiv_map_comp]

end Free

/-! ### Matrices of elementary morphisms -/

section Matrix

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) (R : Type max u v) [CommRing R]
  [HasWeakSheafify J (ModuleCat.{max u v} R)]
  [HasFiniteBiproducts (Sheaf J (ModuleCat.{max u v} R))]

/-- The morphism `⨁_s Λ_{V s} ⟶ ⨁_a Λ_{U a}` whose `(s, a)` component is the finite sum
`∑_k Λ_{φ s a k} ≫ c s a k` of morphisms induced by morphisms of the site followed by scalars. -/
def elementaryMatrix {ι κ : Type} [Finite ι] [Finite κ] (V : ι → C) (U : κ → C)
    {N : ι → κ → ℕ} (φ : ∀ s a, Fin (N s a) → (V s ⟶ U a)) (c : ∀ s a, Fin (N s a) → R) :
    (⨁ fun s ↦ (freeModuleSheaf J R).obj (V s)) ⟶ ⨁ fun a ↦ (freeModuleSheaf J R).obj (U a) :=
  biproduct.matrix fun s a ↦ ∑ k, (freeModuleSheaf J R).map (φ s a k) ≫ smulEnd J (c s a k) _

variable {J R}

/-- An elementary matrix is natural in the objects of the site. -/
lemma elementaryMatrix_naturality {ι κ : Type} [Finite ι] [Finite κ] {V V' : ι → C}
    {U U' : κ → C} {N : ι → κ → ℕ} (σ : ∀ s, V' s ⟶ V s) (τ : ∀ a, U' a ⟶ U a)
    (φ' : ∀ s a, Fin (N s a) → (V' s ⟶ U' a)) (φ : ∀ s a, Fin (N s a) → (V s ⟶ U a))
    (c : ∀ s a, Fin (N s a) → R) (h : ∀ s a k, φ' s a k ≫ τ a = σ s ≫ φ s a k) :
    elementaryMatrix J R V' U' φ' c ≫ biproduct.map (fun a ↦ (freeModuleSheaf J R).map (τ a)) =
      biproduct.map (fun s ↦ (freeModuleSheaf J R).map (σ s)) ≫ elementaryMatrix J R V U φ c := by
  refine biproduct.hom_ext' _ _ fun s ↦ biproduct.hom_ext _ _ fun a ↦ ?_
  simp only [elementaryMatrix, biproduct.ι_matrix_assoc, Category.assoc, biproduct.map_π,
    biproduct.lift_π_assoc, biproduct.ι_map_assoc, biproduct.ι_matrix, biproduct.lift_π,
    Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [← comp_smulEnd, ← Functor.map_comp_assoc, h, Functor.map_comp, Category.assoc]

end Matrix

/-! ### Inverse image along a continuous functor -/

section Pullback

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D] (J : GrothendieckTopology C)
  (K : GrothendieckTopology D) (π : C ⥤ D) [π.IsContinuous J K] (R : Type max u v) [CommRing R]
  [HasWeakSheafify J (ModuleCat.{max u v} R)] [HasWeakSheafify K (ModuleCat.{max u v} R)]
  [HasWeakSheafify J (Type max u v)] [HasWeakSheafify K (Type max u v)]
  [(π.sheafPushforwardContinuous (ModuleCat.{max u v} R) J K).IsRightAdjoint]
  [(π.sheafPushforwardContinuous (Type max u v) J K).IsRightAdjoint]

/-- **Inverse image carries `Λ_U` to `Λ_{π(U)}`, naturally in `U`.** The free module sheaf
commutes with inverse image (`CategoryTheory.Sheaf.composeAndSheafifyFreeSheafPullbackIso`) and so
does the sheafified Yoneda embedding
(`CategoryTheory.Sheaf.sheafifiedYonedaCompSheafPullbackIso`). -/
def freeModuleSheafCompSheafPullbackIso :
    freeModuleSheaf J R ⋙ π.sheafPullback (ModuleCat.{max u v} R) J K ≅
      π ⋙ freeModuleSheaf K R :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (sheafifiedYoneda J)
      (composeAndSheafifyFreeSheafPullbackIso J R K π) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (sheafifiedYonedaCompSheafPullbackIso π J K)
      (composeAndSheafify K (ModuleCat.free R)) ≪≫
    Functor.associator _ _ _

omit [HasWeakSheafify J (ModuleCat.{max u v} R)] [HasWeakSheafify K (ModuleCat.{max u v} R)]
  [HasWeakSheafify J (Type max u v)] [HasWeakSheafify K (Type max u v)]
  [(π.sheafPushforwardContinuous (Type max u v) J K).IsRightAdjoint] in
/-- Inverse image along a continuous functor commutes with multiplication by scalars. -/
lemma sheafPullback_map_smulEnd (r : R) (F : Sheaf J (ModuleCat.{max u v} R)) :
    (π.sheafPullback (ModuleCat.{max u v} R) J K).map (smulEnd J r F) =
      smulEnd K r ((π.sheafPullback (ModuleCat.{max u v} R) J K).obj F) :=
  map_smulEnd_of_adjunction J K (π.sheafAdjunctionContinuous (ModuleCat.{max u v} R) J K)
    (fun _ _ ↦ rfl) r F

omit [π.IsContinuous J K] [HasWeakSheafify J (Type max u v)] [HasWeakSheafify K (Type max u v)]
  [(π.sheafPushforwardContinuous (ModuleCat.{max u v} R) J K).IsRightAdjoint]
  [(π.sheafPushforwardContinuous (Type max u v) J K).IsRightAdjoint] in
/-- **An additive functor compatible with `Λ` and with scalars carries elementary matrices to
elementary matrices.** -/
lemma map_elementaryMatrix [HasFiniteBiproducts (Sheaf J (ModuleCat.{max u v} R))]
    [HasFiniteBiproducts (Sheaf K (ModuleCat.{max u v} R))]
    (L : Sheaf J (ModuleCat.{max u v} R) ⥤ Sheaf K (ModuleCat.{max u v} R)) [L.Additive]
    (β : freeModuleSheaf J R ⋙ L ≅ π ⋙ freeModuleSheaf K R)
    (hL : ∀ (r : R) (F : Sheaf J (ModuleCat.{max u v} R)), L.map (smulEnd J r F) =
      smulEnd K r (L.obj F))
    {ι κ : Type} [Finite ι] [Finite κ] (V : ι → C) (U : κ → C) {N : ι → κ → ℕ}
    (φ : ∀ s a, Fin (N s a) → (V s ⟶ U a)) (c : ∀ s a, Fin (N s a) → R) :
    (L.mapBiproduct _).inv ≫ L.map (elementaryMatrix J R V U φ c) ≫ (L.mapBiproduct _).hom =
      biproduct.map (fun s ↦ β.hom.app (V s)) ≫
        elementaryMatrix K R (fun s ↦ π.obj (V s)) (fun a ↦ π.obj (U a))
          (fun s a k ↦ π.map (φ s a k)) c ≫
        biproduct.map (fun a ↦ β.inv.app (U a)) := by
  refine biproduct.hom_ext' _ _ fun s ↦ biproduct.hom_ext _ _ fun a ↦ ?_
  simp only [Functor.mapBiproduct_inv, Functor.mapBiproduct_hom, Function.comp_def,
    biproduct.ι_desc_assoc, Category.assoc, biproduct.lift_π, biproduct.ι_map_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp]
  simp only [elementaryMatrix, biproduct.ι_matrix_assoc, biproduct.lift_π, Functor.map_sum,
    Functor.map_comp, hL]
  simp only [Functor.comp_obj] at *
  rw [biproduct.map_π, biproduct.lift_π_assoc, Preadditive.sum_comp, Preadditive.comp_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Category.assoc, ← comp_smulEnd, ← Category.assoc, ← Category.assoc]
  congr 1
  exact (NatIso.naturality_2 β (φ s a k)).symm

end Pullback

end CategoryTheory.Sheaf

end

module

public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomPerfectApproximation
public import StacksFrontier.AlgebraicGeometry.Quot.SmallEtaleDerivedTensorPairingSheafHom
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeHomPullbackDataBridge
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedSectionsFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomSmallComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.CohomologyBaseChangeSheafHomTag
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeComp

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedBaseChangeCompSupplement
/-!
# Comparison of the sections of `Lg^*K` with the relative Hom functor (Stacks 08JY)

Let `f : X ⟶ Y` be the morphism of a relative Hom situation, `P` a perfect approximation
`α : P ⟶ 𝓕[0]` of the source module and `K = Rf_*R𝓗om(P, 𝒢[0])`. The proof of Stacks 08JY
identifies `Hom(F_T, G_T)` with `H⁰(T, Lg^*K) = Hom(Lg^*𝒪, Lg^*K)`, naturally in the test scheme
`g : T ⟶ Y`. This file builds the comparison as a morphism of relative Hom functors,
`AlgebraicGeometry.Space.HomSituation.stageComparison`: pullback along the projections
`f_T : X_T ⟶ T`, the unit and counit of `Lf^* ⊣ Rf_*`, the tensor pairing and degree-zero
cohomology through `α`. It also builds the base change map of Stacks 08JQ at a test scheme in the
form adjoint to the comparison, `AlgebraicGeometry.Space.HomSituation.stageBaseChangeMap`,
identifies it with `AlgebraicGeometry.Space.smallEtaleDerivedSheafHomBaseChangeMap`, and
computes its adjoint (`AlgebraicGeometry.Space.HomSituation.homEquiv_symm_stageBaseChangeMap`).

## Implementation notes

Every equation between terms coming from different files is closed by `rfl` only where the two
sides agree syntactically on every subterm containing an `eqToHom` along a non-trivial equation of
morphisms: the kernel unfolds projections such as `NatTrans.app` before comparing arguments, and
reducing `eqToHom` along `t ≫ g = h ≫ f` makes it compare `L(t ≫ g)^*` with `L(h ≫ f)^*`. All
statements are therefore written in the spelling of the cones of test objects, in which the
components of the relative Hom functors unfold.

## References

* [Stacks Project, Tag 08JY](https://stacks.math.columbia.edu/tag/08JY)
* [Stacks Project, Tag 08JQ](https://stacks.math.columbia.edu/tag/08JQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- Composing on both sides with isomorphisms is bijective. -/
private theorem bijective_comp_comp_of_isIso {C : Type*} [Category* C] {X Y Z W : C} (σ : X ⟶ Y)
    [IsIso σ] (τ : Z ⟶ W) [IsIso τ] : Function.Bijective (fun y : Y ⟶ Z => (σ ≫ y) ≫ τ) :=
  ⟨fun y y' h => (cancel_epi σ).1 ((cancel_mono τ).1 h),
    fun y => ⟨inv σ ≫ y ≫ inv τ, by simp⟩⟩

/-- **Bijectivity through an adjunction.** For `L ⊣ R`, isomorphisms `a : O' ⟶ L O` and
`β : K ⟶ R E`, and `b : L K ⟶ E` the adjoint of `β`, the map `x ↦ a ≫ L x ≫ b` from `O ⟶ K` to
`O' ⟶ E` is bijective: it is `x ↦ a ≫ (adj.homEquiv _ _).symm (x ≫ β)`. -/
theorem Adjunction.bijective_comp_map_comp_of_homEquiv {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {O K : C} {O' E : D} (a : O' ⟶ L.obj O) [IsIso a]
    (β : K ⟶ R.obj E) [IsIso β] (b : L.obj K ⟶ E) (hb : (adj.homEquiv K E).symm β = b) :
    Function.Bijective (fun x : O ⟶ K => a ≫ L.map x ≫ b) := by
  have e : (fun x : O ⟶ K => a ≫ L.map x ≫ b) =
      (fun y => a ≫ y) ∘ (adj.homEquiv O E).symm ∘ (fun x => x ≫ β) := by
    funext x
    simp only [Function.comp_apply, ← hb, Adjunction.homEquiv_naturality_left_symm]
  rw [e]
  refine (Function.Bijective.comp ?_ (adj.homEquiv O E).symm.bijective).comp ?_
  · simpa using bijective_comp_comp_of_isIso a (𝟙 _)
  · exact ⟨fun x x' h => (cancel_mono β).1 h, fun y => ⟨y ≫ inv β, by simp⟩⟩

/-- **Bijectivity of pullback along the projections, through an adjunction.**  For comparisons
`e : L_k ≅ L_g ⋙ L_t` and `s : L_f ⋙ L_h ≅ L_k`, an adjunction `L_t ⊣ R_t`, isomorphisms `u`, `a`
and `β : L_g K ⟶ R_t R` whose adjoint is `e⁻¹ ≫ s⁻¹ ≫ L_h b ≫ φ₁ ≫ φ₂`, the map
`x ↦ (u ≫ (L_h a ≫ s(e(L_t x)) ≫ L_h b) ≫ φ₁) ≫ φ₂` is bijective. -/
theorem Functor.bijective_transportHom_conjHom {CY CT CX CX' : Type*} [Category* CY]
    [Category* CT] [Category* CX] [Category* CX'] {Lg : CY ⥤ CT} {Lt : CT ⥤ CX'} {Rt : CX' ⥤ CT}
    {Lf : CY ⥤ CX} {Lh : CX ⥤ CX'} {Lk : CY ⥤ CX'} (e : Lk ≅ Lg ⋙ Lt) (s : Lf ⋙ Lh ≅ Lk)
    (adj : Lt ⊣ Rt) {OY K : CY} {OX H : CX} {O' R₁ R : CX'} (u : O' ⟶ Lh.obj OX) [hu : IsIso u]
    (a : OX ⟶ Lf.obj OY) [ha : IsIso a] (b : Lf.obj K ⟶ H) (φ₁ : Lh.obj H ⟶ R₁) (φ₂ : R₁ ⟶ R)
    (β : Lg.obj K ⟶ Rt.obj R) [hβ : IsIso β]
    (hb : (adj.homEquiv _ _).symm β = e.inv.app K ≫ s.inv.app K ≫ Lh.map b ≫ φ₁ ≫ φ₂) :
    Function.Bijective (fun x : Lg.obj OY ⟶ Lg.obj K =>
      (u ≫ (CategoryStruct.comp (Y := Lh.obj (Lf.obj OY)) (Lh.map a)
        (CategoryStruct.comp (Y := Lh.obj (Lf.obj K)) (transportHom s (conjHom e x))
          (Lh.map b))) ≫ φ₁) ≫ φ₂) := by
  have h := Adjunction.bijective_comp_map_comp_of_homEquiv adj
    (u ≫ Lh.map a ≫ s.hom.app OY ≫ e.hom.app OY) β _ hb
  convert h using 2 with x
  simp [transportHom, conjHom]

/-- **Bijectivity after a tensor-hom adjunction.**  If `x ↦ θ x ≫ G q` is bijective, so is
`x ↦ (σ ≫ (adj.homEquiv _ _).symm (θ x)) ≫ q ≫ τ` for isomorphisms `σ`, `τ`. -/
theorem Adjunction.bijective_comp_homEquiv_symm_comp {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) {Z : Type*} {A : C} {A' B B' B'' : D}
    (σ : A' ⟶ F.obj A) [hσ : IsIso σ] (q : B ⟶ B') (τ : B' ⟶ B'') [hτ : IsIso τ]
    (θ : Z → (A ⟶ G.obj B))
    (hθ : Function.Bijective (fun x => θ x ≫ G.map q)) :
    Function.Bijective (fun x => (σ ≫ (adj.homEquiv _ _).symm (θ x)) ≫ q ≫ τ) := by
  have e : (fun x => (σ ≫ (adj.homEquiv _ _).symm (θ x)) ≫ q ≫ τ) =
      (fun y => (σ ≫ y) ≫ τ) ∘ (adj.homEquiv A B').symm ∘ (fun x => θ x ≫ G.map q) := by
    funext x
    simp [Adjunction.homEquiv_naturality_right_symm]
  rw [e]
  exact (bijective_comp_comp_of_isIso σ τ).comp ((adj.homEquiv A B').symm.bijective.comp hθ)

/-- Reassociating a composite of three morphisms followed by a fourth. -/
theorem Category.assoc_comp_three {C : Type*} [Category* C] {W X Y Z U : C} (a : W ⟶ X)
    (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ U) : (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by
  simp only [Category.assoc]

/-- Regrouping a composite of five morphisms as `(a ≫ (b ≫ c) ≫ d) ≫ e`. -/
theorem Category.comp_comp_comp_comp_eq_assoc {C : Type*} [Category* C] {W X Y Z U V : C}
    (a : W ⟶ X) (b : X ⟶ Y) (c : Y ⟶ Z) (d : Z ⟶ U) (e : U ⟶ V) :
    a ≫ b ≫ c ≫ d ≫ e = (a ≫ (b ≫ c) ≫ d) ≫ e := by
  simp only [Category.assoc]

/-- The inverse of `eqToIso` of the congruence of a family of functors, at an object, is
`eqToHom` of the objects. -/
theorem eqToIso_congrArg_inv_app {C D ι : Type*} [Category* C] [Category* D] (L : ι → C ⥤ D)
    {a b : ι} (h : a = b) (K : C) :
    (eqToIso (congrArg L h)).inv.app K = eqToHom (congrArg (fun m => (L m).obj K) h.symm) := by
  subst h
  rfl

/-- **The base change map for a square isomorphism through a third composite.**  If the
square isomorphism is `s₁⁻¹ ≪≫ s₂ ≪≫ e_g` for comparisons `s₁ : L_c' ≅ L_f ⋙ L_g'` and
`s₂ : L_c' ≅ L_g ⋙ L_f'`, the adjoint of the base change map is `s₂⁻¹` followed by `s₁` and the
image of the counit: the comparison `e_g` cancels. The comparison `s₁` is written `s₁.symm.inv`,
the form in which it arises from transport along `s₁⁻¹`. -/
theorem _root_.Stacks.CategoryTheory.BaseChange.homEquiv_symm_map_symm_trans_trans
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {Lf : A ⥤ B} {Rf : B ⥤ A}
    {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'} {Lg : A ⥤ A'} {Lg' : B ⥤ B'} {Lc Lc' : A ⥤ B'}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (s₁ : Lc' ≅ Lf ⋙ Lg')
    (s₂ : Lc' ≅ Lg ⋙ Lf') (K : B) :
    (adjf'.homEquiv (Lg.obj (Rf.obj K)) (Lg'.obj K)).symm
        (Stacks.CategoryTheory.BaseChange.map adjf adjf' eg (s₁.symm ≪≫ s₂ ≪≫ eg) K) =
      s₂.inv.app (Rf.obj K) ≫ s₁.symm.inv.app (Rf.obj K) ≫ Lg'.map (adjf.counit.app K) := by
  rw [Stacks.CategoryTheory.BaseChange.homEquiv_symm_map]
  simp

namespace PullbackData

section Transport

variable {A : Type*} [Category* A] {D : A → Type*} [∀ a, Category* (D a)] (P : PullbackData A D)
  (pull' : ∀ {a b : A}, (a ⟶ b) → (D b ⥤ D a)) (ε : ∀ {a b : A} (f : a ⟶ b), pull' f ≅ P.pull f)
  {I : Type*} [Category* I] {π : I ⥤ A} {a₀ : A}

/-- Conjugating along the comparison of a transported datum is conjugating along the comparison
of the original datum, read through the transporting isomorphisms (no additivity needed). -/
theorem conjHom_transport_triangle_app {a b d : A} {f : a ⟶ b} {g : b ⟶ d} {k : a ⟶ d}
    (hk : f ≫ g = k) {M N : D d} (x : (pull' g).obj M ⟶ (pull' g).obj N) :
    (ε k).inv.app M ≫ Functor.conjHom ((P.transport pull' ε).triangle hk) x ≫ (ε k).hom.app N =
      Functor.conjHom (P.triangle hk) ((ε g).inv.app M ≫ x ≫ (ε g).hom.app N) := by
  rw [transport_triangle]
  simp only [Functor.conjHom, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Category.assoc, Iso.inv_hom_id_app_assoc, Functor.map_comp]
  have n := (ε f).hom.naturality x
  rw [Iso.inv_hom_id_app, Category.comp_id, reassoc_of% n, Iso.inv_hom_id_app_assoc]

/-- **The relative Hom functor of a transported datum** is that of the original datum, through
the transporting isomorphisms. -/
def relHomTransportIso (hP : P.IsCoherent) (κ : ConeTo π a₀) (M N : D a₀) :
    (P.transport pull' ε).relHomFunctor (transport_isCoherent P pull' ε hP) κ M N ≅
      P.relHomFunctor hP κ M N :=
  NatIso.ofComponents
    (fun i =>
      { hom := ↾fun x => (ε (κ.leg i.unop)).inv.app M ≫ x ≫ (ε (κ.leg i.unop)).hom.app N
        inv := ↾fun x => (ε (κ.leg i.unop)).hom.app M ≫ x ≫ (ε (κ.leg i.unop)).inv.app N
        hom_inv_id := ConcreteCategory.hom_ext _ _
          fun (x : (pull' (κ.leg i.unop)).obj M ⟶ (pull' (κ.leg i.unop)).obj N) => by
            change (ε (κ.leg i.unop)).hom.app M ≫ ((ε (κ.leg i.unop)).inv.app M ≫ x ≫
              (ε (κ.leg i.unop)).hom.app N) ≫ (ε (κ.leg i.unop)).inv.app N = x
            simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id,
              Iso.hom_inv_id_app_assoc]
        inv_hom_id := ConcreteCategory.hom_ext _ _
          fun (x : (P.pull (κ.leg i.unop)).obj M ⟶ (P.pull (κ.leg i.unop)).obj N) => by
            change (ε (κ.leg i.unop)).inv.app M ≫ ((ε (κ.leg i.unop)).hom.app M ≫ x ≫
              (ε (κ.leg i.unop)).inv.app N) ≫ (ε (κ.leg i.unop)).hom.app N = x
            simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
              Iso.inv_hom_id_app_assoc] })
    (fun {i j} g => ConcreteCategory.hom_ext _ _ fun x =>
      P.conjHom_transport_triangle_app pull' ε (κ.w g.unop) x)

end Transport

section CompIso

variable {A : Type*} [Category* A] {D : A → Type*} [∀ a, Category* (D a)] (P : PullbackData A D)

/-- **The comparison of a triangle against a second factorisation**, when the composition
comparisons of the datum are inverses `C⁻¹` of given compositors: the inverse of the comparison of
`f' ≫ g = h ≫ f`, followed by the comparison of `h ≫ f`, is `C f' g` followed by the
identification of the two composites and `(C h f)⁻¹`. -/
theorem triangle_inv_app_comp_compIso_hom_app {a b b' c : A} {f : b ⟶ c} {h : a ⟶ b}
    {f' : a ⟶ b'} {g : b' ⟶ c} (hk : f' ≫ g = h ≫ f)
    (C₁ : P.pull g ⋙ P.pull f' ≅ P.pull (f' ≫ g)) (C₂ : P.pull f ⋙ P.pull h ≅ P.pull (h ≫ f))
    (h₁ : P.compIso f' g = C₁.symm) (h₂ : P.compIso h f = C₂.symm) (K : D c)
    (E : (P.pull (f' ≫ g)).obj K ⟶ (P.pull (h ≫ f)).obj K)
    (hE : (eqToHom (congrArg (fun m : a ⟶ c => P.pull m) hk)).app K = E) {W : D a}
    (q : (P.pull h).obj ((P.pull f).obj K) ⟶ W) :
    (P.triangle hk).inv.app K ≫ (P.triangle (rfl : h ≫ f = h ≫ f)).hom.app K ≫ q =
      C₁.hom.app K ≫ E ≫ C₂.inv.app K ≫ q := by
  rw [triangle_rfl, triangle_eq, h₁, h₂, ← hE]
  simp

end CompIso

section PrecompInv

variable {A : Type*} [Category* A] {D : A → Type*} [∀ a, Category* (D a)] (P : PullbackData A D)
  {I I₁ : Type*} [Category* I] [Category* I₁] {π : I ⥤ A} {a₀ a₁ : A}

/-- The inverse component of `CategoryTheory.PullbackData.relHomPrecompIso`. -/
theorem relHomPrecompIso_inv_app (hP : P.IsCoherent) (κ : ConeTo π a₀) (Φ : I₁ ⥤ I)
    (k : a₁ ⟶ a₀) (κ₁ : ConeTo (Φ ⋙ π) a₁) (hκ : ∀ i, κ₁.leg i ≫ k = κ.leg (Φ.obj i))
    (M N : D a₀) (i : I₁) (α : P.relHomObj κ M N (Φ.obj i)) :
    (P.relHomPrecompIso hP κ Φ k κ₁ hκ M N).inv.app (Opposite.op i) α =
      Functor.transportHom (P.triangle (hκ i)).symm α :=
  rfl

end PrecompInv

end PullbackData

end CategoryTheory

namespace AlgebraicGeometry.Space

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The identification of the derived pullbacks along two equal morphisms, in the spelling of the
pullback datum `AlgebraicGeometry.Space.toposDerivedPullbackData`, is the identification
`AlgebraicGeometry.Space.smallEtaleDerivedModulePullbackCongr`. -/
theorem toposDerivedPullbackData_eqToIso {X Y : AlgebraicSpaces B S hS} {k₁ k₂ : X ⟶ Y}
    (e : k₁ = k₂) (e' : k₁ = k₂) :
    eqToIso (congrArg (fun m => (toposDerivedPullbackData B S hS).pull m) e) =
      smallEtaleDerivedModulePullbackCongr B S hS e' := by
  subst e
  rfl

/-- Two identifications of derived pullbacks along equal morphisms, in the spelling of the
pullback datum, compose to the identification `smallEtaleDerivedModulePullbackCongr`. -/
theorem toposDerivedPullbackData_eqToIso_symm_trans {X Y : AlgebraicSpaces B S hS}
    {k₀ k₁ k₂ : X ⟶ Y} (e : k₀ = k₁) (e' : k₀ = k₂) (w : k₁ = k₂) :
    (eqToIso (congrArg (fun m => (toposDerivedPullbackData B S hS).pull m) e)).symm ≪≫
        eqToIso (congrArg (fun m => (toposDerivedPullbackData B S hS).pull m) e') =
      smallEtaleDerivedModulePullbackCongr B S hS w := by
  subst e
  subst e'
  rfl

namespace HomSituation

variable (v : HomSituation B S hS) (Pm : toposDerived B S hS v.X)

/-- Pullback of sections along the projections `X_T ⟶ T` followed by the unit and the counit of
`Lf^* ⊣ Rf_*`: `Hom(Lg^*𝒪, Lg^*K) ⟶ Hom(Lh^*𝒪_X, Lh^*R𝓗om(P, 𝒢[0]))`. -/
def stageBaseChangeCounit :
    (toposDerivedPullbackData B S hS).relHomFunctor (toposDerivedPullbackData_isCoherent B S hS)
        (schemesOverCone v.base) (structureDerived v.base)
        ((smallEtaleDerivedModulePushforward B S hS v.f).obj
          (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
            ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))) ⟶
      (toposDerivedPullbackData B S hS).relHomFunctor (toposDerivedPullbackData_isCoherent B S hS)
        (baseChangeProjectionCone v.f) (structureDerived v.X)
          (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
            ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)) :=
  relHomBaseChange v.f (toposDerivedPullbackData B S hS)
      (toposDerivedPullbackData_isCoherent B S hS) (structureDerived v.base)
      ((smallEtaleDerivedModulePushforward B S hS v.f).obj
        (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
          ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))) ≫
    (toposDerivedPullbackData B S hS).relHomBimap (toposDerivedPullbackData_isCoherent B S hS)
      (baseChangeProjectionCone v.f) (smallEtaleDerivedModulePullbackUnitIso v.f).inv
      ((smallEtaleDerivedAdjunction B S hS v.f).counit.app
        (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
          ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)))

/-- The tensor pairing of Stacks 08JY, `Hom(Lh^*𝒪_X, Lh^*R𝓗om(P, 𝒢[0])) ⟶ Hom(Lh^*P, Lh^*𝒢[0])`. -/
def stageTensorPairing :
    (toposDerivedPullbackData B S hS).relHomFunctor (toposDerivedPullbackData_isCoherent B S hS)
        (baseChangeProjectionCone v.f) (structureDerived v.X)
          (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
            ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)) ⟶
      (toposDerivedPullbackData B S hS).relHomFunctor (toposDerivedPullbackData_isCoherent B S hS)
        (baseChangeProjectionCone v.f) Pm
          ((𝟭 (DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS v.X)))).obj
            ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)) :=
  PullbackData.relHomTensorPairing (smallEtaleDerivedTensorCompatibility B S hS)
    (toposDerivedPullbackData_isCoherent B S hS) (baseChangeProjectionCone v.f)
    ((smallEtaleDerivedTensorStructureIso v.X Pm).hom :)
    ((smallEtaleDerivedTensorSheafHomAdjunction B S hS v.X Pm).counit.app
      ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G) :)

variable {Pm} (α : Pm ⟶ (DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.F)
  (hiso : ∀ i : ℤ, -1 < i →
    IsIso ((DerivedCategory.homologyFunctor (toposModules B S hS v.X) i).map α))
  (hepi : Epi ((DerivedCategory.homologyFunctor (toposModules B S hS v.X) (-1)).map α))

/-- Degree-zero cohomology through the approximation `α : P ⟶ 𝓕[0]`,
`Hom(Lh^*P, Lh^*𝒢[0]) ⟶ Hom(h^*𝓕, h^*𝒢)`. -/
def stageDegreeZero :
    (toposDerivedPullbackData B S hS).relHomFunctor (toposDerivedPullbackData_isCoherent B S hS)
        (baseChangeProjectionCone v.f) Pm
          ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G) ⟶
      (toposPullbackData B S hS).relHomFunctor (toposPullbackData_isCoherent B S hS)
        (baseChangeProjectionCone v.f) v.F v.G :=
  (toposPullbackData B S hS).relHomDegreeZero
    (fun f => smallEtaleDerivedModulePullback B S hS f)
    (fun f => smallEtaleDerivedModulePullbackComparison B S hS f)
    (hL := fun f => isLeftDerivedFunctor_smallEtaleDerivedModulePullback f)
    (hcomp := fun f g => isIso_smallEtaleDerivedComp f g)
    (hid := fun X => isIso_smallEtaleDerivedIdLift X)
    (hZ := fun j => isLE_smallEtaleDerivedModulePullback_leg_of_approximation
      (baseChangeProjectionCone v.f) α hiso j)
    (hθ := fun j => isIso_degreeZeroCompare_toposPullbackData_of_approximation
      (baseChangeProjectionCone v.f) α hiso hepi j)
    (baseChangeProjectionCone v.f) Pm α (toposPullbackData_isCoherent B S hS) v.G

/-- The base change `X_T` of the morphism of a relative Hom situation along a test scheme is a
fibre product, in the spelling of the cones of test objects. -/
theorem isPullback_baseChangeSquare (T : v.SchemesOver) :
    IsPullback ((baseChangeProjectionCone v.f).leg T) ((baseChangeSpacesInclusion v.f).app T) v.f
      ((schemesOverCone v.base).leg T) :=
  AlgebraicSpaces.isPullback_fiberProduct B S hS v.f ((schemesOverToOver v.base).obj T).hom

/-- `X_T ⟶ T ⟶ base` is `X_T ⟶ X ⟶ base`, in the spelling of the cones of test objects. -/
abbrev StageTriangle₁ (T : v.SchemesOver) : Prop :=
  (baseChangeSpacesInclusion v.f).app T ≫ (schemesOverCone v.base).leg T =
    (baseChangeProjectionConeOverBase v.f).leg T

/-- `X_T ⟶ X ⟶ base` is the structure morphism of `X_T` over the base, in the spelling of the
cones of test objects. -/
abbrev StageTriangle₂ (T : v.SchemesOver) : Prop :=
  (baseChangeProjectionCone v.f).leg T ≫ v.f = (baseChangeProjectionConeOverBase v.f).leg T

/-- **The square isomorphism of the stage** `Lh^* ∘ Lf^* ≅ L(f_T ≫ g)^*`, through the composition
comparisons of the pullback datum `AlgebraicGeometry.Space.toposDerivedPullbackData` at the two
factorisations of `X_T ⟶ base` and the comparison of Stacks 0D6D for `f_T ≫ g`. -/
def stageSquareIso (T : v.SchemesOver) (h₁ : v.StageTriangle₁ T) (h₂ : v.StageTriangle₂ T) :
    (toposDerivedPullbackData B S hS).pull v.f ⋙
        (toposDerivedPullbackData B S hS).pull ((baseChangeProjectionCone v.f).leg T) ≅
      smallEtaleDerivedModulePullback B S hS
        ((baseChangeSpacesInclusion v.f).app T ≫ (schemesOverCone v.base).leg T) :=
  ((toposDerivedPullbackData B S hS).triangle h₂).symm ≪≫
    (toposDerivedPullbackData B S hS).triangle h₁ ≪≫
    smallEtaleDerivedModulePullbackCompIso B S hS ((baseChangeSpacesInclusion v.f).app T)
      ((schemesOverCone v.base).leg T)

/-- **The square isomorphism of the stage is that of Stacks 08JQ.** -/
theorem stageSquareIso_eq (T : v.SchemesOver) (h₁ : v.StageTriangle₁ T) (h₂ : v.StageTriangle₂ T)
    (w : (baseChangeProjectionCone v.f).leg T ≫ v.f =
      (baseChangeSpacesInclusion v.f).app T ≫ (schemesOverCone v.base).leg T) :
    v.stageSquareIso T h₁ h₂ = smallEtaleDerivedModulePullbackSquareIso B S hS v.f
      ((schemesOverCone v.base).leg T) ((baseChangeSpacesInclusion v.f).app T)
      ((baseChangeProjectionCone v.f).leg T) w := by
  rw [stageSquareIso, PullbackData.triangle_eq, PullbackData.triangle_eq,
    toposDerivedPullbackData_compIso_eq_smallEtaleDerivedModulePullbackCompIso_symm,
    toposDerivedPullbackData_compIso_eq_smallEtaleDerivedModulePullbackCompIso_symm]
  simp only [Iso.trans_symm, Iso.symm_symm_eq, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]
  rw [toposDerivedPullbackData_eqToIso_symm_trans h₂.symm h₁.symm w]
  rfl

variable (Pm) in
/-- **The base change map of Stacks 08JQ at a stage, through the square isomorphism
`AlgebraicGeometry.Space.HomSituation.stageSquareIso`**:
`Lg^*Rf_*R𝓗om(P, 𝒢[0]) ⟶ Rf_{T*}Lh^*R𝓗om(P, 𝒢[0]) ⟶ Rf_{T*}R𝓗om(Lh^*P, h^*𝒢[0])`. -/
def stageBaseChangeMap (T : v.SchemesOver) (h₁ : v.StageTriangle₁ T) (h₂ : v.StageTriangle₂ T) :
    (smallEtaleDerivedModulePullback B S hS ((schemesOverCone v.base).leg T)).obj
        ((smallEtaleDerivedModulePushforward B S hS v.f).obj
          (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
            ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))) ⟶
      (smallEtaleDerivedModulePushforward B S hS ((baseChangeSpacesInclusion v.f).app T)).obj
        (((smallEtaleDerivedSheafHom B S hS ((baseChangeSpaces v.f).obj T)).obj
          (op ((smallEtaleDerivedModulePullback B S hS
            ((baseChangeProjectionCone v.f).leg T)).obj Pm))).obj
          (DerivedCategory.Q.obj
            (((modulePullback B S hS ((baseChangeProjectionCone v.f).leg T)).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj
                ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj v.G)))) :=
  Stacks.CategoryTheory.BaseChange.map (smallEtaleDerivedAdjunction B S hS v.f)
      (smallEtaleDerivedAdjunction B S hS ((baseChangeSpacesInclusion v.f).app T))
      (smallEtaleDerivedModulePullbackCompIso B S hS ((baseChangeSpacesInclusion v.f).app T)
        ((schemesOverCone v.base).leg T))
      (v.stageSquareIso T h₁ h₂) (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
          ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)) ≫
    (smallEtaleDerivedModulePushforward B S hS ((baseChangeSpacesInclusion v.f).app T)).map
      (smallEtaleDerivedPullbackSheafHomMap ((baseChangeProjectionCone v.f).leg T) Pm
          ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G) ≫
        ((smallEtaleDerivedSheafHom B S hS ((baseChangeSpaces v.f).obj T)).obj
          (op ((smallEtaleDerivedModulePullback B S hS
            ((baseChangeProjectionCone v.f).leg T)).obj Pm))).map
          (smallEtaleDerivedModulePullbackQComparison ((baseChangeProjectionCone v.f).leg T)
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj v.G)))

variable (Pm) in
/-- The base change map of the stage is the base change map of Stacks 08JQ. -/
theorem stageBaseChangeMap_eq (T : v.SchemesOver) (h₁ : v.StageTriangle₁ T)
    (h₂ : v.StageTriangle₂ T)
    (w : (baseChangeProjectionCone v.f).leg T ≫ v.f =
      (baseChangeSpacesInclusion v.f).app T ≫ (schemesOverCone v.base).leg T) :
    v.stageBaseChangeMap Pm T h₁ h₂ = smallEtaleDerivedSheafHomBaseChangeMap v.f
      ((schemesOverCone v.base).leg T) ((baseChangeSpacesInclusion v.f).app T)
      ((baseChangeProjectionCone v.f).leg T) w Pm
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj v.G) := by
  rw [stageBaseChangeMap, v.stageSquareIso_eq T h₁ h₂ w]
  rfl

variable (Pm) in
/-- **The adjoint of the base change map of a stage**: under `Lf_T^* ⊣ Rf_{T*}` it is the
comparison of the two factorisations of `X_T ⟶ base`, `Lh^*` of the counit of `Lf^* ⊣ Rf_*`, the
map of Stacks 08JF and the comparison from the derived to the degreewise pullback of `𝒢[0]`. -/
theorem homEquiv_symm_stageBaseChangeMap (T : v.SchemesOver) (h₁ : v.StageTriangle₁ T)
    (h₂ : v.StageTriangle₂ T) :
    ((smallEtaleDerivedAdjunction B S hS ((baseChangeSpacesInclusion v.f).app T)).homEquiv _ _).symm
        (v.stageBaseChangeMap Pm T h₁ h₂) =
      ((toposDerivedPullbackData B S hS).triangle h₁).inv.app
          ((smallEtaleDerivedModulePushforward B S hS v.f).obj
            (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
              ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))) ≫
        ((toposDerivedPullbackData B S hS).triangle h₂).symm.inv.app
            ((smallEtaleDerivedModulePushforward B S hS v.f).obj
              (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
                ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))) ≫
        ((toposDerivedPullbackData B S hS).pull ((baseChangeProjectionCone v.f).leg T)).map
          ((smallEtaleDerivedAdjunction B S hS v.f).counit.app
            (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
              ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))) ≫
        smallEtaleDerivedPullbackSheafHomMap ((baseChangeProjectionCone v.f).leg T) Pm
          ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G) ≫
        ((smallEtaleDerivedSheafHom B S hS ((baseChangeSpaces v.f).obj T)).obj
          (op ((smallEtaleDerivedModulePullback B S hS
            ((baseChangeProjectionCone v.f).leg T)).obj Pm))).map
          (smallEtaleDerivedModulePullbackQComparison ((baseChangeProjectionCone v.f).leg T)
            ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj v.G)) :=
  ((smallEtaleDerivedAdjunction B S hS
    ((baseChangeSpacesInclusion v.f).app T)).homEquiv_naturality_right_symm _ _).trans
    ((congrArg (· ≫ _) (Stacks.CategoryTheory.BaseChange.homEquiv_symm_map_symm_trans_trans
      (smallEtaleDerivedAdjunction B S hS v.f)
      (smallEtaleDerivedAdjunction B S hS ((baseChangeSpacesInclusion v.f).app T))
      (smallEtaleDerivedModulePullbackCompIso B S hS ((baseChangeSpacesInclusion v.f).app T)
        ((schemesOverCone v.base).leg T))
      ((toposDerivedPullbackData B S hS).triangle h₂)
      ((toposDerivedPullbackData B S hS).triangle h₁)
        (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
          ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G)))).trans
    (Category.assoc_comp_three _ _ _ _))

/-- **The comparison of Stacks 08JY at a stage**: the sections `Hom(Lg^*𝒪, Lg^*K)` of the
functor of Stacks 08JX, part (2), at `K = Rf_*R𝓗om(P, 𝒢[0])`, go to `Hom(h^*𝓕, h^*𝒢)` by pullback
along the projections `X_T ⟶ T`, the unit and counit of `Lf^* ⊣ Rf_*`, the tensor pairing and
degree-zero cohomology through `α : P ⟶ 𝓕[0]`. -/
def stageComparison :
    (toposDerivedPullbackData B S hS).relHomFunctor (toposDerivedPullbackData_isCoherent B S hS)
        (schemesOverCone v.base) (structureDerived v.base)
        ((smallEtaleDerivedModulePushforward B S hS v.f).obj
          (((smallEtaleDerivedSheafHom B S hS v.X).obj (op Pm)).obj
            ((DerivedCategory.singleFunctor (toposModules B S hS v.X) 0).obj v.G))) ⟶
      (toposPullbackData B S hS).relHomFunctor (toposPullbackData_isCoherent B S hS)
        (baseChangeProjectionCone v.f) v.F v.G :=
  v.stageBaseChangeCounit Pm ≫ v.stageTensorPairing Pm ≫ v.stageDegreeZero α hiso hepi

/-- The component of the comparison of Stacks 08JY at a test scheme is the composite of the
components of its three steps. -/
theorem stageComparison_app (T : v.SchemesOver) (x) :
    (v.stageComparison α hiso hepi).app (op T) x = (v.stageDegreeZero α hiso hepi).app (op T)
      ((v.stageTensorPairing Pm).app (op T) ((v.stageBaseChangeCounit Pm).app (op T) x)) :=
  rfl

end HomSituation

end AlgebraicGeometry.Space

end

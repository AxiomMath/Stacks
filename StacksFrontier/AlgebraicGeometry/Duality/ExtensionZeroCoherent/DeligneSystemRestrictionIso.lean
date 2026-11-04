module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.BoundedCoherentTStructure
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTargetTriangle
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.DeligneSystemTruncation

/-!
# The identification of Stacks 0G2H, from its core case

Let `j : U ⟶ X` be an open immersion of Noetherian schemes and let `(K_n)` be a Deligne system
with value `K` on `U`. [Stacks, Tag 0G2H] asserts that the canonical restriction map

`colim_n Hom_X(K_n, L) ⟶ Hom_U(K, L|_U)`

is bijective for every `L` in `D^b_{Coh}(𝒪_X)`, that is, that
`AlgebraicGeometry.DeligneSystem.restrictionNatTrans` is an isomorphism of functors.

This file deduces that statement from its core case: the case in which the source system is
replaced by one of its one-degree truncations and the target is concentrated in a single degree.

## Implementation notes

The proof of [Stacks, Tag 0G2H] has three parts. The first two are reductions, and are carried
out here.

1. *Dévissage in the target.* From a distinguished triangle `L ⟶ M ⟶ N ⟶ L⟦1⟧` the
   identification at `L` and `N` gives it at `M`, by the five lemma
   (`CategoryTheory.restrictionLifting_target_triangle`). Applied to the triangles of the
   canonical truncations this reduces the target to one with a single nonzero cohomology sheaf
   (`CategoryTheory.restrictionLifting_of_single_degree`).
2. *Dévissage in the source.* An inverse system of distinguished triangles whose outer vertex
   systems satisfy the identification has middle system satisfying it
   (`CategoryTheory.restrictionLifting_triangle`); applied to the `t`-structure truncations of the
   system this reduces the source to a system concentrated in a single degree
   (`CategoryTheory.restrictionLifting_of_truncGELE`). The Stacks Project uses the brutal
   truncations of the complex `𝓘^n𝓕^•` instead, whose termwise split short exact sequences give
   the same triangles; the `t`-structure truncations only need the `t`-structure on
   `D^b_{Coh}(𝒪_X)` of `AlgebraicGeometry.boundedCoherentTStructure`.
3. *The core case*, the bijectivity of `colim_n Ext^i_X(𝓘^n𝓕, 𝓖) ⟶ Ext^i_U(𝓕|_U, 𝓖|_U)` for
   coherent `𝓕` and `𝓖`, is the hypothesis `hcore` of
   `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core`, stated as the
   identification for a one-degree truncation of the system against a target concentrated in a
   single degree. It is proved as `AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE`,
   and the resulting unconditional form of the tag is
   `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans`.

Both reductions need a uniform degree range of the system: every term of `𝓘^n𝓕^i` is a subsheaf
of `𝓕^i`, so `𝓘^n𝓕^•` has the strict bounds of `𝓕^•`
(`AlgebraicGeometry.DeligneSystem.exists_isGE_isLE_system`).

## Main results

* `CategoryTheory.restrictionLifting_of_single_degree`: the dévissage in the target.
* `CategoryTheory.restrictionLifting_of_truncGELE`: the dévissage in the source.
* `CategoryTheory.restrictionLifting_of_core`: the two together.
* `AlgebraicGeometry.exists_isGE_isLE_boundedCoherentTStructure`: every object of
  `D^b_{Coh}(𝒪_X)` lies in a degree range for the `t`-structure.
* `AlgebraicGeometry.DeligneSystem.exists_isGE_isLE_system`: the inverse system of a Deligne
  system has a uniform degree range, that of its complex.
* `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_restrictionLifting`: the
  elementwise identification at every object gives the isomorphism of functors.
* `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core`: **[Stacks, Tag 0G2H]**
  from its core case.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01YA](https://stacks.math.columbia.edu/tag/01YA)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open CategoryTheory.Triangulated Opposite

attribute [local instance] CategoryTheory.uliftCategory
attribute [local instance] HasDerivedCategory.standard

universe v u u'

namespace CategoryTheory

/-! ## The dévissage in the target -/

section Target

variable {𝒟 : Type u} [Category.{v} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] [IsTriangulated 𝒟]
  {𝒞 : Type u'} [Category.{v} 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

/-- The induction on the length of the degree range of the target underlying the dévissage in the
target: if `R` identifies `colim_n Mor(F_n, -)` with `colim_n Mor(R F_n, R -)` at every object
concentrated in a single degree, then it does so at every object of a bounded degree range. -/
public lemma restrictionLifting_of_single_degree_aux (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) [R.Additive]
    [R.CommShift ℤ] [R.IsTriangulated] (t : TStructure 𝒟)
    (hsingle : ∀ (q : ℤ) (N : 𝒟), t.IsGE N q → t.IsLE N q → RestrictionLifting F R N) :
    ∀ (k : ℕ) (a b : ℤ), b ≤ a + k → ∀ N : 𝒟, t.IsGE N a → t.IsLE N b →
      RestrictionLifting F R N := by
  intro k
  induction k with
  | zero =>
    intro a b hb N hGE hLE
    exact hsingle a N hGE (t.isLE_of_le N b a (by simpa using hb))
  | succ k ih =>
    intro a b hb N hGE hLE
    by_cases hba : b ≤ a
    · exact hsingle a N hGE (t.isLE_of_le N b a hba)
    -- The truncation triangle, inverse-rotated so that `N` is its third object.
    have hTi : ((t.triangleLEGE a (a + 1) rfl).obj N).invRotate ∈ distTriang 𝒟 :=
      inv_rot_of_distTriang _ (t.triangleLEGE_distinguished a (a + 1) rfl N)
    have hg1 : t.IsGE ((t.truncGE (a + 1)).obj N) (a + 1) := inferInstance
    have hl1 : t.IsLE ((t.truncGE (a + 1)).obj N) b := inferInstance
    have hg2 : t.IsGE (((t.truncGE (a + 1)).obj N)⟦(-1 : ℤ)⟧) (a + 2) :=
      t.isGE_shift _ (a + 1) (-1) (a + 2) (by omega)
    have hl2 : t.IsLE (((t.truncGE (a + 1)).obj N)⟦(-1 : ℤ)⟧) (b + 1) :=
      t.isLE_shift _ b (-1) (b + 1) (by omega)
    have h₁ : RestrictionLifting F R (((t.truncGE (a + 1)).obj N)⟦(-1 : ℤ)⟧) :=
      ih (a + 2) (b + 1) (by push_cast at hb ⊢; omega) _ hg2 hl2
    have h₂ : RestrictionLifting F R ((t.truncLE a).obj N) :=
      ih a a (by omega) _ inferInstance inferInstance
    have h₁' : RestrictionLifting F R ((((t.truncGE (a + 1)).obj N)⟦(-1 : ℤ)⟧)⟦(1 : ℤ)⟧) :=
      ih (a + 1) b (by push_cast at hb ⊢; omega) _
        (t.isGE_shift _ (a + 2) 1 (a + 1) (by omega))
        (t.isLE_shift _ (b + 1) 1 b (by omega))
    have h₂' : RestrictionLifting F R (((t.truncLE a).obj N)⟦(1 : ℤ)⟧) :=
      ih (a - 1) (a - 1) (by omega) _
        (t.isGE_shift _ a 1 (a - 1) (by omega))
        (t.isLE_shift _ a 1 (a - 1) (by omega))
    exact restrictionLifting_target_triangle F R hTi h₁ h₂ h₁' h₂'

/-- **The dévissage in the target of the identification of [Stacks, Tag 0G2H].** If `R` identifies
`colim_n Mor(F_n, -)` with `colim_n Mor(R F_n, R -)` at every object concentrated in a single
degree for a `t`-structure `t`, then it does so at every object with a bounded degree range.

This is the first reduction in the proof of the tag: it is what reduces the target to one with a
single nonzero cohomology sheaf. The inductive step is
`CategoryTheory.restrictionLifting_target_triangle`, applied to the inverse rotation of the
truncation triangle `τ^{≤a}N ⟶ N ⟶ τ^{≥a+1}N ⟶ (τ^{≤a}N)⟦1⟧`, whose third object is `N`. -/
public lemma restrictionLifting_of_single_degree (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) [R.Additive]
    [R.CommShift ℤ] [R.IsTriangulated] (t : TStructure 𝒟)
    (hsingle : ∀ (q : ℤ) (N : 𝒟), t.IsGE N q → t.IsLE N q → RestrictionLifting F R N)
    {a b : ℤ} (N : 𝒟) (hGE : t.IsGE N a) (hLE : t.IsLE N b) :
    RestrictionLifting F R N :=
  restrictionLifting_of_single_degree_aux F R t hsingle (b - a).toNat a b (by omega) N hGE hLE

end Target

/-! ## The dévissage in the source -/

section Source

variable {𝒟 : Type u} [Category.{v} 𝒟] [Preadditive 𝒟] [HasZeroObject 𝒟] [HasShift 𝒟 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒟 n).Additive] [Pretriangulated 𝒟] [IsTriangulated 𝒟]
  {𝒞 : Type u'} [Category.{v} 𝒞] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞]

omit [IsTriangulated 𝒟] [Preadditive 𝒞] [HasZeroObject 𝒞] [HasShift 𝒞 ℤ]
  [∀ (n : ℤ), (shiftFunctor 𝒞 n).Additive] [Pretriangulated 𝒞] in
/-- An inverse sequence concentrated in a single degree satisfies the identification as soon as
its one-degree truncation does, because it is isomorphic to that truncation. This is the base case
of the dévissage in the source. -/
public lemma restrictionLifting_of_single (R : 𝒟 ⥤ 𝒞) (t : TStructure 𝒟) (F : ℕᵒᵖ ⥤ 𝒟) (a : ℤ)
    (hGE : ∀ n, t.IsGE (F.obj n) a) (hLE : ∀ n, t.IsLE (F.obj n) a) (N : 𝒟)
    (H : RestrictionLifting (F ⋙ t.truncGELE a a) R N) : RestrictionLifting F R N :=
  RestrictionLifting.of_natIso (t.truncGELESelfIso F a hGE hLE) R N H

omit [IsTriangulated 𝒟] in
/-- The inductive step of the dévissage in the source: if the identification holds for the two
truncations `(τ^{≤a}F_n)` and `(τ^{≥a+1}F_n)` at every object, then it holds for `(F_n)`.

This is `CategoryTheory.restrictionLifting_triangle` for the inverse system of truncation
triangles `τ^{≤a}F_n ⟶ F_n ⟶ τ^{≥a+1}F_n ⟶ (τ^{≤a}F_n)⟦1⟧`; the statement for the shifted system
`(τ^{≤a}F_n)⟦1⟧`, which the five lemma also needs, is the statement for `(τ^{≤a}F_n)` at the
object `N⟦-1⟧`, transported by `CategoryTheory.RestrictionLifting.map_source`. -/
public lemma restrictionLifting_triangleLEGE (R : 𝒟 ⥤ 𝒞) [R.Additive] [R.CommShift ℤ]
    [R.IsTriangulated] (t : TStructure 𝒟) (F : ℕᵒᵖ ⥤ 𝒟) (a : ℤ)
    (h₁ : ∀ N, RestrictionLifting (F ⋙ t.truncLE a) R N)
    (h₃ : ∀ N, RestrictionLifting (F ⋙ t.truncGE (a + 1)) R N) (N : 𝒟) :
    RestrictionLifting F R N := by
  have hKp : ∀ M : 𝒟, RestrictionLifting ((F ⋙ t.truncLE a) ⋙ shiftFunctor 𝒟 (1 : ℤ)) R M :=
    fun M => (h₁ (M⟦(-1 : ℤ)⟧)).map_source (shiftFunctor 𝒟 (1 : ℤ)) (shiftFunctor 𝒞 (1 : ℤ)) R
      (R.commShiftIso (1 : ℤ)) ((shiftFunctorCompIsoId 𝒟 (-1 : ℤ) 1 (by decide)).app M)
  exact restrictionLifting_triangle R (F ⋙ t.triangleLEGE a (a + 1) rfl)
    (fun n => t.triangleLEGE_distinguished a (a + 1) rfl (F.obj n)) N (h₁ N) (h₃ N)
    (h₃ (N⟦(1 : ℤ)⟧)) (hKp N)

/-- The induction on the length of the degree range of the source underlying the dévissage in the
source. -/
public lemma restrictionLifting_of_truncGELE_aux (R : 𝒟 ⥤ 𝒞) [R.Additive] [R.CommShift ℤ]
    [R.IsTriangulated] (t : TStructure 𝒟) :
    ∀ (k : ℕ) (a b : ℤ), b = a + k → ∀ F : ℕᵒᵖ ⥤ 𝒟, (∀ n, t.IsGE (F.obj n) a) →
      (∀ n, t.IsLE (F.obj n) b) →
      (∀ p : ℤ, a ≤ p → p ≤ b → ∀ N, RestrictionLifting (F ⋙ t.truncGELE p p) R N) →
      ∀ N, RestrictionLifting F R N := by
  intro k
  induction k with
  | zero =>
    intro a b hb F hGE hLE H N
    have hba : b = a := by simpa using hb
    subst hba
    exact restrictionLifting_of_single R t F b hGE hLE N (H b le_rfl le_rfl N)
  | succ k ih =>
    intro a b hb F hGE hLE H N
    have h₁ : ∀ M : 𝒟, RestrictionLifting (F ⋙ t.truncLE a) R M := by
      intro M
      refine restrictionLifting_of_single R t (F ⋙ t.truncLE a) a (fun n => ?_) (fun n => ?_) M ?_
      · have := hGE n
        exact inferInstanceAs (t.IsGE ((t.truncLE a).obj (F.obj n)) a)
      · exact inferInstanceAs (t.IsLE ((t.truncLE a).obj (F.obj n)) a)
      · exact RestrictionLifting.of_natIso
          (Functor.isoWhiskerLeft F (t.truncLECompTruncGELEIso a)) R M
          (H a le_rfl (by push_cast at hb ⊢; omega) M)
    have h₃ : ∀ M : 𝒟, RestrictionLifting (F ⋙ t.truncGE (a + 1)) R M := by
      refine ih (a + 1) b (by push_cast at hb ⊢; omega) (F ⋙ t.truncGE (a + 1))
        (fun n => inferInstanceAs (t.IsGE ((t.truncGE (a + 1)).obj (F.obj n)) (a + 1)))
        (fun n => ?_) (fun p hp hp' M => ?_)
      · have := hLE n
        exact inferInstanceAs (t.IsLE ((t.truncGE (a + 1)).obj (F.obj n)) b)
      · exact RestrictionLifting.of_natIso
          (Functor.isoWhiskerLeft F (t.truncGECompTruncGELEIso hp)) R M
          (H p (by omega) hp' M)
    exact restrictionLifting_triangleLEGE R t F a h₁ h₃ N

/-- **The dévissage in the source of the identification of [Stacks, Tag 0G2H].** Let `(F_n)` be an
inverse sequence whose terms lie in the degree range `[a, b]` for a `t`-structure `t`. If, for
every `a ≤ p ≤ b`, the one-degree truncation system `(τ^{≥p}τ^{≤p}F_n)` satisfies the
identification at every object, then so does `(F_n)`.

This is the second reduction in the proof of the tag. The Stacks Project performs it with the
brutal truncations of the complex `𝓘^n𝓕^•`, whose termwise split short exact sequences give
inverse systems of distinguished triangles; the triangles of the `t`-structure truncations serve
the same purpose. The inductive step is
`CategoryTheory.restrictionLifting_triangle`, the five lemma in the source variable. -/
public lemma restrictionLifting_of_truncGELE (R : 𝒟 ⥤ 𝒞) [R.Additive] [R.CommShift ℤ]
    [R.IsTriangulated] (t : TStructure 𝒟) {a b : ℤ} (hab : a ≤ b) (F : ℕᵒᵖ ⥤ 𝒟)
    (hGE : ∀ n, t.IsGE (F.obj n) a) (hLE : ∀ n, t.IsLE (F.obj n) b)
    (H : ∀ p : ℤ, a ≤ p → p ≤ b → ∀ N, RestrictionLifting (F ⋙ t.truncGELE p p) R N)
    (N : 𝒟) : RestrictionLifting F R N :=
  restrictionLifting_of_truncGELE_aux R t (b - a).toNat a b (by omega) F hGE hLE H N

/-- **The two dévissages of [Stacks, Tag 0G2H] together.** Let `(F_n)` be an inverse sequence whose
terms lie in the degree range `[a, b]`, and suppose every object of `𝒟` has a bounded degree
range. If, for every `a ≤ p ≤ b`, the one-degree truncation system `(τ^{≥p}τ^{≤p}F_n)` satisfies
the identification at every object concentrated in a single degree, then `(F_n)` satisfies it at
every object.

The hypothesis is the core case of the tag: in the situation of the tag it is the bijectivity of
`colim_n Ext^i_X(𝓘^n𝓕, 𝓖) ⟶ Ext^i_U(𝓕|_U, 𝓖|_U)` for coherent `𝓕` and `𝓖`. -/
public lemma restrictionLifting_of_core (R : 𝒟 ⥤ 𝒞) [R.Additive] [R.CommShift ℤ]
    [R.IsTriangulated] (t : TStructure 𝒟) {a b : ℤ} (hab : a ≤ b) (F : ℕᵒᵖ ⥤ 𝒟)
    (hGE : ∀ n, t.IsGE (F.obj n) a) (hLE : ∀ n, t.IsLE (F.obj n) b)
    (hbdd : ∀ N : 𝒟, ∃ c d : ℤ, t.IsGE N c ∧ t.IsLE N d)
    (hcore : ∀ p q : ℤ, a ≤ p → p ≤ b → ∀ N : 𝒟, t.IsGE N q → t.IsLE N q →
      RestrictionLifting (F ⋙ t.truncGELE p p) R N)
    (N : 𝒟) : RestrictionLifting F R N := by
  refine restrictionLifting_of_truncGELE R t hab F hGE hLE (fun p hp hp' M => ?_) N
  obtain ⟨c, d, hc, hd⟩ := hbdd M
  exact restrictionLifting_of_single_degree (F ⋙ t.truncGELE p p) R t
    (fun q P hq hq' => hcore p q hp hp' P hq hq') M hc hd

end Source

/-! ## From the elementwise identification to the isomorphism of functors -/

section Bridge

variable {𝒟 : Type u} [Category.{v} 𝒟] {𝒞 : Type u'} [Category.{v} 𝒞]

/-- The class of a morphism `f : F_n ⟶ X` in `colim_m Mor(F_m, X)`, the colimit being the one over
the lifted index category that `CategoryTheory.Pro.coyonedaColim` uses. -/
private abbrev stageCls (F : ℕᵒᵖ ⥤ 𝒟) {X : 𝒟} {n : ℕ} (f : F.obj (op n) ⟶ X) :
    (Pro.coyonedaColim (Pro.liftedInverseSequence F)).obj X :=
  (colimit.ι ((Pro.liftedInverseSequence F).op ⋙ coyoneda)
    (op (Pro.liftedIndexObj.{v} n))).app X f

/-- Every element of `colim_n Mor(F_n, X)` is the class of a morphism out of some term. -/
private lemma stageCls_surjective (F : ℕᵒᵖ ⥤ 𝒟) (X : 𝒟)
    (x : (Pro.coyonedaColim (Pro.liftedInverseSequence F)).obj X) :
    ∃ (n : ℕ) (f : F.obj (op n) ⟶ X), x = stageCls F f := by
  obtain ⟨i, f, h⟩ := FunctorToTypes.jointly_surjective'
    ((Pro.liftedInverseSequence F).op ⋙ coyoneda) X x
  rcases i with ⟨⟨⟨n⟩⟩⟩
  exact ⟨n, f, h⟩

/-- Precomposing with a transition does not change the class. -/
private lemma stageCls_transition (F : ℕᵒᵖ ⥤ 𝒟) {X : 𝒟} {n m : ℕ} (h : n ≤ m)
    (f : F.obj (op n) ⟶ X) : stageCls F (InverseSequence.tr F h ≫ f) = stageCls F f := by
  have he := congrArg (fun z => z.app X)
    (colimit.w ((Pro.liftedInverseSequence F).op ⋙ coyoneda) (Pro.liftedIndexHom.{v} h).op)
  exact ConcreteCategory.congr_hom he f

/-- Two morphisms with the same class agree after a transition. -/
private lemma stageCls_eq (F : ℕᵒᵖ ⥤ 𝒟) {X : 𝒟} {n m : ℕ} (f : F.obj (op n) ⟶ X)
    (g : F.obj (op m) ⟶ X) (h : stageCls F f = stageCls F g) :
    ∃ (k : ℕ) (hn : n ≤ k) (hm : m ≤ k),
      InverseSequence.tr F hn ≫ f = InverseSequence.tr F hm ≫ g := by
  set S := Pro.liftedInverseSequence F with hS
  set D := (S.op ⋙ coyoneda) ⋙ (evaluation 𝒟 (Type v)).obj X with hD
  set E := colimitObjIsoColimitCompEvaluation (S.op ⋙ coyoneda) X with hE
  have he : colimit.ι D (op (Pro.liftedIndexObj.{v} n)) f =
      colimit.ι D (op (Pro.liftedIndexObj.{v} m)) g := by
    have hh : (((colimit.ι (S.op ⋙ coyoneda) (op (Pro.liftedIndexObj.{v} n))).app X) ≫ E.hom) f =
        (((colimit.ι (S.op ⋙ coyoneda) (op (Pro.liftedIndexObj.{v} m))).app X) ≫ E.hom) g :=
      congrArg E.hom h
    simpa only [hE, colimitObjIsoColimitCompEvaluation_ι_app_hom] using hh
  obtain ⟨i, a, b, hab⟩ := (Limits.Types.FilteredColimit.colimit_eq_iff D).mp he
  refine ⟨i.unop.objDown.down.unop, leOfHom a.unop.down.unop, leOfHom b.unop.down.unop, ?_⟩
  have hmap {i j : (ULiftHom (ULift.{v, 0} ℕᵒᵖ))ᵒᵖ} (c : i ⟶ j) :
      S.map c.unop = InverseSequence.tr F (leOfHom c.unop.down.unop) := by
    change (ULift.downFunctor ⋙ F).map c.unop.down = _
    congr 1
  change S.map a.unop ≫ f = S.map b.unop ≫ g at hab
  rwa [hmap a, hmap b] at hab

/-- **From the elementwise identification to an isomorphism of functors.** Let `F` be an inverse
sequence whose restriction along `R` is the constant sequence at `A`, and let `θ` be a
transformation `colim_n Mor(F_n, -) ⟶ Mor(A, R -)` sending the class of `f : F_n ⟶ N` to
`R f` precomposed with the `n`-th component of that identification. If `R` identifies
`colim_n Mor(F_n, N)` with `colim_n Mor(R F_n, R N)` elementwise for every `N`, then `θ` is an
isomorphism.

The two halves of `CategoryTheory.RestrictionLifting` are exactly surjectivity and injectivity of
`θ` at each object, once the classes in the colimit are written through
`CategoryTheory.Pro.liftedIndexObj`. -/
private lemma isIso_of_stage_formula (F : ℕᵒᵖ ⥤ 𝒟) (R : 𝒟 ⥤ 𝒞) (A : 𝒞)
    (e : F ⋙ R ≅ (Functor.const ℕᵒᵖ).obj A)
    (θ : Pro.coyonedaColim (Pro.liftedInverseSequence F) ⟶ R ⋙ coyoneda.obj (op A))
    (hθ : ∀ (n : ℕ) (N : 𝒟) (g : F.obj (op n) ⟶ N),
      θ.app N (stageCls F g) = e.inv.app (op n) ≫ R.map g)
    (h : ∀ N, RestrictionLifting F R N) : IsIso θ := by
  have hnat : ∀ {n m : ℕ} (hnm : n ≤ m),
      e.inv.app (op m) ≫ R.map (InverseSequence.tr F hnm) = e.inv.app (op n) := by
    intro n m hnm
    have hh := e.inv.naturality (homOfLE hnm).op
    change (𝟙 A) ≫ e.inv.app (op n) = e.inv.app (op m) ≫ R.map (InverseSequence.tr F hnm) at hh
    rw [Category.id_comp] at hh
    exact hh.symm
  have happ : ∀ N : 𝒟, Function.Bijective (θ.app N) := by
    intro N
    constructor
    · intro x y hxy
      obtain ⟨n, f, rfl⟩ := stageCls_surjective F N x
      obtain ⟨m, g, rfl⟩ := stageCls_surjective F N y
      rw [hθ, hθ] at hxy
      have hn : n ≤ max n m := le_max_left _ _
      have hm : m ≤ max n m := le_max_right _ _
      have hcancel : R.map (InverseSequence.tr F hn ≫ f) = R.map (InverseSequence.tr F hm ≫ g) :=
        (cancel_epi (e.inv.app (op (max n m)))).mp <| by
          rwa [R.map_comp, R.map_comp, ← Category.assoc, ← Category.assoc, hnat hn, hnat hm]
      obtain ⟨q, hq, heq⟩ := (h N).eq (max n m) (InverseSequence.tr F hn ≫ f)
        (InverseSequence.tr F hm ≫ g) hcancel
      have hf : stageCls F f = stageCls F (InverseSequence.tr F (hn.trans hq) ≫ f) :=
        (stageCls_transition F (hn.trans hq) f).symm
      have hg : stageCls F g = stageCls F (InverseSequence.tr F (hm.trans hq) ≫ g) :=
        (stageCls_transition F (hm.trans hq) g).symm
      rw [hf, hg]
      congr 1
      rw [← tr_comp F hq hn, ← tr_comp F hq hm, Category.assoc, Category.assoc]
      exact heq
    · intro φ
      change A ⟶ R.obj N at φ
      obtain ⟨m, hm, f, hf⟩ := (h N).lift 0 (e.hom.app (op 0) ≫ φ)
      refine ⟨stageCls F f, ?_⟩
      rw [hθ, hf, ← Category.assoc, hnat hm, ← Category.assoc, e.inv_hom_id_app]
      exact Category.id_comp φ
  have : ∀ N : 𝒟, IsIso (θ.app N) := fun N => (isIso_iff_bijective _).mpr (happ N)
  exact NatIso.isIso_of_isIso_app θ

end Bridge

end CategoryTheory

namespace AlgebraicGeometry

/-! ## The scheme-level statement -/

variable {U X : Scheme.{u}}

/-- **Every object of `D^b_{Coh}(𝒪_X)` has a bounded degree range** for the `t`-structure of
`AlgebraicGeometry.boundedCoherentTStructure`: that is what cohomological boundedness says. -/
public lemma exists_isGE_isLE_boundedCoherentTStructure (N : BoundedCoherentDerived X) :
    ∃ c d : ℤ, (boundedCoherentTStructure X).IsGE N c ∧
      (boundedCoherentTStructure X).IsLE N d := by
  obtain ⟨⟨c, hc⟩, ⟨d, hd⟩⟩ := N.property.1
  refine ⟨c, d, ?_, ?_⟩
  · exact (ObjectProperty.tStructure_isGE_iff (boundedCoherentDerived X)
      DerivedCategory.TStructure.t N c).mpr
      ((DerivedCategory.isGE_iff N.obj c).mpr (fun i hi => hc i hi))
  · exact (ObjectProperty.tStructure_isLE_iff (boundedCoherentDerived X)
      DerivedCategory.TStructure.t N d).mpr
      ((DerivedCategory.isLE_iff N.obj d).mpr (fun i hi => hd i hi))

namespace DeligneSystem

variable {j : U ⟶ X} [IsOpenImmersion j] [IsNoetherian X] (D : DeligneSystem j)

/-- **The identification of [Stacks, Tag 0G2H] from its elementwise form.** If restriction along
`j` identifies `colim_n Hom_X(K_n, L)` with `colim_n Hom_U(K_n|_U, L|_U)` elementwise for every
`L`, then the canonical restriction transformation
`AlgebraicGeometry.DeligneSystem.restrictionNatTrans` is an isomorphism, which is the assertion of
the tag.

The transformation sends the class of `g : K_n ⟶ L` to the restriction of `g` read through the
identification of `K` with `K_n|_U`, by
`AlgebraicGeometry.DeligneSystem.restrictionNatTrans_app_ι`, so this is
`CategoryTheory.isIso_of_stage_formula`. -/
public lemma isIso_restrictionNatTrans_of_restrictionLifting (K : BoundedCoherentDerived U)
    (e : D.system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K))
    (h : ∀ L : BoundedCoherentDerived X,
      RestrictionLifting D.system (restrictBoundedCoherent j) L) :
    IsIso (D.restrictionNatTrans K e) :=
  CategoryTheory.isIso_of_stage_formula D.system (restrictBoundedCoherent j)
    ((boundedCoherentDerived U).ι.obj K) e (D.restrictionNatTrans K e)
    (fun n L g => D.restrictionNatTrans_app_ι K e (op (CategoryTheory.Pro.liftedIndexObj n)) L g)
    h

/-- **Stacks Project, Tag 0G2H** for a system of a known degree range, from its core case. Let
`j : U ⟶ X` be an open immersion of Noetherian schemes, let `(K_n)` be a Deligne system with value
`K` on `U`, and suppose the terms of `(K_n)` lie in the degree range `[a, b]` of the `t`-structure
on `D^b_{Coh}(𝒪_X)`. If, for every `a ≤ p ≤ b`, the one-degree truncation system
`(τ^{≥p}τ^{≤p}K_n)` satisfies the tag's identification elementwise against every target
concentrated in a single degree, then the canonical restriction transformation

`colim_n Mor_X(K_n, -) ⟶ Mor_U(K, (-)|_U)`

is an isomorphism: `colim_n Hom_X(K_n, L) = Hom_U(K, L|_U)` for every `L` in `D^b_{Coh}(𝒪_X)`.

The hypothesis `hcore` is the core case of the tag, the bijectivity of
`colim_n Ext^i_X(𝓘^n𝓕, 𝓖) ⟶ Ext^i_U(𝓕|_U, 𝓖|_U)` for coherent `𝓕` and `𝓖`; the two reductions
are `CategoryTheory.restrictionLifting_of_core`.

See `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans_of_core` for the version without
the degree range hypothesis. -/
public theorem isIso_restrictionNatTrans_of_core_range (K : BoundedCoherentDerived U)
    (e : D.system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K))
    {a b : ℤ} (hab : a ≤ b)
    (hGE : ∀ n, (boundedCoherentTStructure X).IsGE (D.system.obj n) a)
    (hLE : ∀ n, (boundedCoherentTStructure X).IsLE (D.system.obj n) b)
    (hcore : ∀ p q : ℤ, a ≤ p → p ≤ b → ∀ L : BoundedCoherentDerived X,
      (boundedCoherentTStructure X).IsGE L q → (boundedCoherentTStructure X).IsLE L q →
      RestrictionLifting (D.system ⋙ (boundedCoherentTStructure X).truncGELE p p)
        (restrictBoundedCoherent j) L) :
    IsIso (D.restrictionNatTrans K e) :=
  D.isIso_restrictionNatTrans_of_restrictionLifting K e fun L =>
    CategoryTheory.restrictionLifting_of_core (restrictBoundedCoherent j)
      (boundedCoherentTStructure X) hab D.system hGE hLE
      exists_isGE_isLE_boundedCoherentTStructure hcore L

/-- A term of `𝓘^n𝓕^•` vanishes wherever the corresponding term of `𝓕^•` does. -/
private lemma isZero_powers_complex_X (n : ℕ) (i : ℤ) (h : IsZero (D.complex.X i)) :
    IsZero ((D.powers.complex n).X i) :=
  (D.powers.termIso n i).isZero_iff.mpr
    (@IsZero.of_mono _ _ _ _ _
      (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple D.idealSheaf n (D.complex.X i)).ι
      (SheafOfModules.Submodule.instMonoι _) h)

/-- **The ideal-power subcomplexes inherit a lower bound of the complex.** Each term of `𝓘^n𝓕^•`
is a subsheaf of the corresponding term of `𝓕^•`, hence zero wherever that one is. -/
public lemma isStrictlyGE_powers_complex (a : ℤ) (ha : D.complex.IsStrictlyGE a) (n : ℕ) :
    (D.powers.complex n).IsStrictlyGE a := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  have := ha
  exact D.isZero_powers_complex_X n i (D.complex.isZero_of_isStrictlyGE a i hi)

/-- **The ideal-power subcomplexes inherit an upper bound of the complex.** -/
public lemma isStrictlyLE_powers_complex (b : ℤ) (hb : D.complex.IsStrictlyLE b) (n : ℕ) :
    (D.powers.complex n).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  have := hb
  exact D.isZero_powers_complex_X n i (D.complex.isZero_of_isStrictlyLE b i hi)

/-- A lower bound for the complex of a Deligne system is a lower bound, for the `t`-structure of
`D^b_{Coh}(𝒪_X)`, for every term of its inverse system. -/
public lemma isGE_system_obj (a : ℤ) (ha : ∀ n : ℕ, (D.powers.complex n).IsStrictlyGE a)
    (n : ℕᵒᵖ) : (boundedCoherentTStructure X).IsGE (D.system.obj n) a := by
  have := ha n.unop
  have h1 : DerivedCategory.TStructure.t.IsGE
      ((Functor.ofOpSequence D.powers.transition ⋙ DerivedCategory.Q).obj n) a :=
    inferInstanceAs ((DerivedCategory.Q.obj (D.powers.complex n.unop)).IsGE a)
  exact (ObjectProperty.tStructure_isGE_iff (boundedCoherentDerived X)
    DerivedCategory.TStructure.t (D.system.obj n) a).mpr
    (@Triangulated.TStructure.isGE_of_iso _ _ _ _ _ _ _ DerivedCategory.TStructure.t _ _
      (D.representation.app n).symm a h1)

/-- An upper bound for the complex of a Deligne system is an upper bound, for the `t`-structure of
`D^b_{Coh}(𝒪_X)`, for every term of its inverse system. -/
public lemma isLE_system_obj (b : ℤ) (hb : ∀ n : ℕ, (D.powers.complex n).IsStrictlyLE b)
    (n : ℕᵒᵖ) : (boundedCoherentTStructure X).IsLE (D.system.obj n) b := by
  have := hb n.unop
  have h1 : DerivedCategory.TStructure.t.IsLE
      ((Functor.ofOpSequence D.powers.transition ⋙ DerivedCategory.Q).obj n) b :=
    inferInstanceAs ((DerivedCategory.Q.obj (D.powers.complex n.unop)).IsLE b)
  exact (ObjectProperty.tStructure_isLE_iff (boundedCoherentDerived X)
    DerivedCategory.TStructure.t (D.system.obj n) b).mpr
    (@Triangulated.TStructure.isLE_of_iso _ _ _ _ _ _ _ DerivedCategory.TStructure.t _ _
      (D.representation.app n).symm b h1)

/-- **The inverse system of a Deligne system has a uniform degree range.** It is the degree range
of the bounded complex `𝓕^•` the system is built from: every term of `𝓘^n𝓕^i` is a subsheaf of
`𝓕^i`, so `𝓘^n𝓕^•` has the strict bounds of `𝓕^•`, which pass to the derived category. -/
public lemma exists_isGE_isLE_system :
    ∃ a b : ℤ, a ≤ b ∧ (∀ n, (boundedCoherentTStructure X).IsGE (D.system.obj n) a) ∧
      (∀ n, (boundedCoherentTStructure X).IsLE (D.system.obj n) b) := by
  obtain ⟨a, ha⟩ := D.exists_isStrictlyGE
  obtain ⟨b, hb⟩ := D.exists_isStrictlyLE
  have ha' : D.complex.IsStrictlyGE (min a b) := by
    have := ha
    exact D.complex.isStrictlyGE_of_ge (min a b) a (min_le_left a b)
  have hb' : D.complex.IsStrictlyLE (max a b) := by
    have := hb
    exact D.complex.isStrictlyLE_of_le b (max a b) (le_max_right a b)
  exact ⟨min a b, max a b, (min_le_left a b).trans (le_max_left a b),
    D.isGE_system_obj (min a b) (D.isStrictlyGE_powers_complex (min a b) ha'),
    D.isLE_system_obj (max a b) (D.isStrictlyLE_powers_complex (max a b) hb')⟩

/-- **Stacks Project, Tag 0G2H**, from its core case. Let `j : U ⟶ X` be an open immersion of
Noetherian schemes and let `(K_n)` be a Deligne system with value `K` on `U`. If every one-degree
truncation system `(τ^{≥p}τ^{≤p}K_n)` satisfies the tag's identification elementwise against
every target concentrated in a single degree, then the canonical restriction transformation

`colim_n Mor_X(K_n, -) ⟶ Mor_U(K, (-)|_U)`

is an isomorphism: `colim_n Hom_X(K_n, L) = Hom_U(K, L|_U)` for every `L` in `D^b_{Coh}(𝒪_X)`,
which is the assertion of the tag.

The hypothesis `hcore` is the core case of the tag, the bijectivity of
`colim_n Ext^i_X(𝓘^n𝓕, 𝓖) ⟶ Ext^i_U(𝓕|_U, 𝓖|_U)` for coherent `𝓕` and `𝓖`, whose `i = 0` case is
[Stacks, Tag 01YB] and whose `i > 0` case is an Artin-Rees induction. It is proved as
`AlgebraicGeometry.DeligneSystem.restrictionLifting_truncGELE`, which gives the unconditional
form `AlgebraicGeometry.DeligneSystem.isIso_restrictionNatTrans`. -/
public theorem isIso_restrictionNatTrans_of_core (K : BoundedCoherentDerived U)
    (e : D.system ⋙ restrictBoundedCoherent j ≅
      (Functor.const ℕᵒᵖ).obj ((boundedCoherentDerived U).ι.obj K))
    (hcore : ∀ p q : ℤ, ∀ L : BoundedCoherentDerived X,
      (boundedCoherentTStructure X).IsGE L q → (boundedCoherentTStructure X).IsLE L q →
      RestrictionLifting (D.system ⋙ (boundedCoherentTStructure X).truncGELE p p)
        (restrictBoundedCoherent j) L) :
    IsIso (D.restrictionNatTrans K e) := by
  obtain ⟨a, b, hab, hGE, hLE⟩ := D.exists_isGE_isLE_system
  exact D.isIso_restrictionNatTrans_of_core_range K e hab hGE hLE
    (fun p q _ _ L hq hq' => hcore p q L hq hq')

end DeligneSystem

end AlgebraicGeometry

end

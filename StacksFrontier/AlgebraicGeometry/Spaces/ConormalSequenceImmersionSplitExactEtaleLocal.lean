module

public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentAdicPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleOfImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceImmersionSplitExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalSequenceSplitting
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 05ZB, the étale-local clause: the restricted conormal sequence is split exact

Let `i : Z ⟶ X` be an immersion of algebraic spaces over `Bb`, with structure morphism
`b : X ⟶ Bb`, and let `{φ_k : X_k ⟶ X}` be an étale covering of `X` (Stacks 041E).  Write
`Z_k = Z ×_X X_k`, with projections `i_k : Z_k ⟶ X_k` and `a_k : Z_k ⟶ Z`, and suppose each
`i_k` has a left inverse `g_k` over `Bb`.  [Stacks Project, Tag 05ZB] says that then the
canonical sequence of [Stacks Project, Tag 05ZA]
```
  0 ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb} ⟶ 0
```
is étale locally split exact.  This file proves that **the inverse image along every `a_k` of
the whole short complex of `i`** — its conormal term `a_k^*𝒞_{Z/X}`, its first arrow
`a_k^*` of the first arrow of `i`, and its second arrow `a_k^*c_i` — admits a
`CategoryTheory.ShortComplex.Splitting`.  So its first arrow is a monomorphism, it is exact at
the middle term and its second arrow is a split epimorphism.

## The route

It is the source's: étale localization reduces the clause to the global clause at `i_k`, which
is `AlgebraicGeometry.Space.nonempty_conormalSequenceOfImmersion_splitting`.  What has to be
supplied is an isomorphism of short complexes between the inverse image along `a_k` of the
sequence of `i` and the sequence of `i_k` over `φ_k ≫ b`:

* on the conormal terms, the canonical map `a_k^*𝒞_{Z/X} ⟶ 𝒞_{Z_k/X_k}` of
  [Stacks Project, Tag 04CP], which is invertible at a cartesian square with étale transverse
  edge by [Stacks Project, Tag 04CO]
  (`AlgebraicGeometry.Space.isIso_conormalMapOfImmersions_of_isPullback_of_isEtale`);
* on the middle terms, the comparison `a_k^*i^*Ω_{X/Bb} ≅ i_k^*φ_k^*Ω_{X/Bb}` of
  [Stacks Project, Tag 03LU] across the square, followed by `i_k^*` of the comparison map
  `φ_k^*Ω_{X/Bb} ⟶ Ω_{X_k/Bb}`, invertible by [Stacks Project, Tag 04CU];
* on the right-hand terms, the comparison map `a_k^*Ω_{Z/Bb} ⟶ Ω_{Z_k/Bb}`, invertible by
  [Stacks Project, Tag 04CU] because `a_k`, a base change of `φ_k`, is étale.

The right-hand square commutes by uniqueness of the comparison maps of [Stacks Project, Tag 04CX]
(`AlgebraicGeometry.Space.comp_comp_eq_eqToHom_comp`).  The left-hand square is the
**naturality of the first arrow of [Stacks Project, Tag 05ZA] along the square**, proved here.
It splits into a change of source along `a_k` and a change of ambient space along `φ_k`; the
second is `AlgebraicGeometry.Space.kernelConormalFirstMap_compPullbackMap`, and the first is
`AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_comp_map_kernelConormalFirstMap` below:
the inverse image along `a` of the first arrow of `i`, read through `(a ≫ i)^* ≅ a^*i^*`, is the
first arrow of `a ≫ i` restricted along the containment `𝓘_i ⊆ 𝓘_{a ≫ i}` of kernel ideal
sheaves.  Both are transposes along `(a ≫ i)^* ⊣ (a ≫ i)_*` of the restriction of `d_{X/Bb}` to
`𝓘_i` followed by a unit of adjunction, and the two units agree by the unit coherence of the
comparison `(a ≫ i)^* ≅ a^*i^*` of [Stacks Project, Tag 03LU].

The two ways of reading the conormal term — through the kernel ideal sheaf
(`AlgebraicGeometry.Space.conormalModuleOfImmersionKernelPullbackIso`) and through the canonical
map of [Stacks Project, Tag 04CP] — are matched by
`AlgebraicGeometry.Space.conormalMapOfImmersions_eq_kernelIdeal`: both maps of ideal sheaves are
pinned by their composite with the inclusion into the structure sheaf, which is a monomorphism.

## Main results

* `AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_comp_map_kernelConormalFirstMap`: the
  first arrow of [Stacks Project, Tag 05ZA] under a change of source.
* `AlgebraicGeometry.Space.conormalMapOfImmersions_comp_conormalSequenceFirstMapOfImmersion`:
  the first arrow of [Stacks Project, Tag 05ZA] is natural along a commutative square of
  immersions, the conormal terms being compared by the canonical map of
  [Stacks Project, Tag 04CP].
* `AlgebraicGeometry.Space.nonempty_map_conormalSequenceOfImmersion_splitting_of_isPullback`:
  the restriction of the sequence of `i` along one cartesian square with étale transverse edge
  is split exact, when the restricted immersion has a left inverse over `Bb`.
* `AlgebraicGeometry.Space.nonempty_map_conormalSequenceOfImmersion_splitting_of_isEtaleCovering`:
  **Stacks 05ZB, the étale-local clause in full.**

## References

* [Stacks Project, Tag 05ZB](https://stacks.math.columbia.edu/tag/05ZB)
* [Stacks Project, Tag 05ZA](https://stacks.math.columbia.edu/tag/05ZA)
* [Stacks Project, Tag 04CO](https://stacks.math.columbia.edu/tag/04CO)
* [Stacks Project, Tag 04CP](https://stacks.math.columbia.edu/tag/04CP)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace CategoryTheory

/-- **Transport of a component of a natural isomorphism along equalities of objects.**  Let
`σ : P ⋙ Q ≅ R ⋙ T`, let `A = A'` and `Y' = Y`, and let `m` be `m'` conjugated by the
transports.  Then `Q.map` of a transport, `σ.hom.app A`, `T.map m` and a transport compose to
`σ.hom.app A' ≫ T.map m'`.

Stated at variables, so that the identification of the two spellings of the objects is made
once, by `subst`, before any geometric term is in sight. -/
theorem map_eqToHom_comp_app_comp_map_comp_eqToHom {C D D' E : Type*} [Category C] [Category D]
    [Category D'] [Category E] (P : C ⥤ D) (Q : D ⥤ E) (R : C ⥤ D') (T : D' ⥤ E)
    (σ : P ⋙ Q ≅ R ⋙ T) {A A' : C} (hA : A = A') {Y Y' : D'} (hY : Y' = Y)
    (m : R.obj A ⟶ Y) (m' : R.obj A' ⟶ Y')
    (hm : m = eqToHom (congrArg R.obj hA) ≫ m' ≫ eqToHom hY)
    (e₁ : P.obj A' = P.obj A) (e₂ : T.obj Y = T.obj Y') :
    Q.map (eqToHom e₁) ≫ σ.hom.app A ≫ T.map m ≫ eqToHom e₂ = σ.hom.app A' ≫ T.map m' := by
  subst hA hY hm
  simp

/-- Cancelling an isomorphism in front of a composite with a tail, at plain variables. -/
theorem Iso.hom_comp_comp_comp_eq_of_inv_comp {C : Type*} [Category C] {A₀ A₁ B₀ B₁ V W : C}
    (e : A₀ ≅ A₁) (p : A₁ ⟶ B₁) (q : B₁ ⟶ V) (r : A₀ ⟶ B₀) (s : B₀ ⟶ V) (t : V ⟶ W)
    (h : e.inv ≫ r ≫ s = p ≫ q) : e.hom ≫ p ≫ q ≫ t = r ≫ s ≫ t := by
  rw [← reassoc_of% h, Iso.hom_inv_id_assoc]

/-- **The arithmetic of the naturality of the first arrow along a square**, at plain variables:
a component `sqI` of a square comparison, written out by `hA` and `hB`, a factorisation `hm`, a
naturality square `nat`, the comparison `kc` across the change of ambient space and the
comparison `sp` across the change of source assemble to the naturality of the first arrow. -/
theorem comp_comp_eq_of_square_chain {C : Type*} [Category C]
    {A A₁ A₂ A₃ D D' E F G H K K₁ : C}
    (sqI : A ⟶ D) (hI : A ⟶ A₁) (eI : A₁ ⟶ A₂) (cI : A₂ ⟶ D) (hA : sqI = hI ≫ eI ≫ cI)
    (m : D ⟶ E) (m₁ : D ⟶ D') (m₂ : D' ⟶ E) (hm : m = m₁ ≫ m₂) (k' : E ⟶ F)
    (n : A₂ ⟶ A₃) (cJ : A₃ ⟶ D') (nat : cI ≫ m₁ = n ≫ cJ)
    (k : A₃ ⟶ G) (cΩ : G ⟶ H) (pφ : H ⟶ F) (kc : cJ ≫ m₂ ≫ k' = k ≫ cΩ ≫ pφ)
    (ak : A ⟶ K) (sqΩ : K ⟶ H) (hΩ : K ⟶ K₁) (eΩ : K₁ ⟶ G) (hB : sqΩ = hΩ ≫ eΩ ≫ cΩ)
    (sp : hI ≫ eI ≫ n ≫ k ≫ cΩ ≫ pφ = ak ≫ hΩ ≫ eΩ ≫ cΩ ≫ pφ) :
    sqI ≫ m ≫ k' = ak ≫ sqΩ ≫ pφ := by
  subst hA hB hm
  simp only [Category.assoc]
  rw [reassoc_of% nat, kc, sp]

/-- **Transporting the canonical map of conormal modules to the kernel ideal sheaves**, at plain
variables: two pairs of mutually inverse transports `(e, e')` and `(f, f')` and the equation `hG`
relating the two middle composites give the canonical map, conjugated, in terms of the other. -/
theorem Functor.map_comp_comp_comp_eq_of_eqToHom {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {Pc Pk Ik : C} (p : Pc ⟶ Pk) (e : Pk ⟶ Ik) (e' : Ik ⟶ Pk) (he : e ≫ e' = 𝟙 Pk)
    {W₁ W₂ W₃ Y Y' : D} (sqZ : F.obj Pk ⟶ W₁) (N : W₁ ⟶ Y) (sqI : F.obj Ik ⟶ W₂) (M : W₂ ⟶ Y')
    (f : Y ⟶ Y') (f' : Y' ⟶ Y) (hf : f ≫ f' = 𝟙 Y) (q : Y ⟶ W₃)
    (hG : F.map e' ≫ sqZ ≫ N ≫ f = sqI ≫ M) :
    F.map p ≫ (sqZ ≫ N) ≫ q = F.map (p ≫ e) ≫ sqI ≫ M ≫ f' ≫ q := by
  rw [← reassoc_of% hG, reassoc_of% hf, ← F.map_comp_assoc]
  simp [he]

/-- **The second square of the étale-local comparison**, at plain variables. -/
theorem Iso.comp_comp_eq_of_hom_comp {C : Type*} [Category C] {A A' G₁ H P R Q : C}
    (e : A ≅ A') (sq : A ⟶ H) (x : A' ⟶ G₁) (y : G₁ ⟶ H) (hs : sq = e.hom ≫ x ≫ y)
    (p : H ⟶ P) (c : P ⟶ R) (ac : A ⟶ Q) (ca : Q ⟶ R)
    (h₂ : e.inv ≫ ac ≫ ca = x ≫ y ≫ p ≫ c) : (sq ≫ p) ≫ c = ac ≫ ca := by
  subst hs
  simp only [Category.assoc]
  rw [← h₂, Iso.hom_inv_id_assoc]

/-- The forward morphism of `a.symm ≪≫ eqToIso p`, at plain variables. -/
theorem Iso.symm_trans_eqToIso_hom {C : Type*} [Category C] {X Y Z : C} (a : Y ≅ X)
    (p : Y = Z) : (a.symm ≪≫ eqToIso p).hom = a.inv ≫ eqToHom p :=
  rfl

/-- The inverse morphism of `a.symm ≪≫ eqToIso p`, at plain variables. -/
theorem Iso.symm_trans_eqToIso_inv {C : Type*} [Category C] {X Y Z : C} (a : Y ≅ X)
    (p : Y = Z) : (a.symm ≪≫ eqToIso p).inv = eqToHom p.symm ≫ a.hom :=
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] preservesZeroMorphisms_modulePullback

/-! ### The first arrow under a change of source -/

section SourceChange

variable {X Z Z' Bb : AlgebraicSpaces B S hS}

/-- The unit of `i^* ⊣ i_*` followed by the direct image of a morphism is its transpose, here at
the transpose along `a^* ⊣ a_*` of the comparison `a^*i^* ⟶ (a ≫ i)^*` of
[Stacks Project, Tag 03LU], followed by the comparison of direct images.  Its own declaration, so
that the kernel checks the two spellings of the composite separately. -/
theorem unit_comp_modulePushforward_map_homEquiv_comp_eq_homEquiv (a : Z' ⟶ Z) (i : Z ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackAdjunction B S hS i).unit.app M ≫
        (modulePushforward B S hS i).map
          ((modulePullbackAdjunction B S hS a).homEquiv ((modulePullback B S hS i).obj M)
            ((modulePullback B S hS (a ≫ i)).obj M)
            ((modulePullbackCompIso B S hS a i).hom.app M)) ≫
        (modulePushforwardCompIso B S hS a i).hom.app ((modulePullback B S hS (a ≫ i)).obj M) =
      (modulePullbackAdjunction B S hS i).homEquiv M _
          ((modulePullbackAdjunction B S hS a).homEquiv _ _
            ((modulePullbackCompIso B S hS a i).hom.app M)) ≫
        (modulePushforwardCompIso B S hS a i).hom.app _ :=
  (Category.assoc _ _ _).symm.trans
    (eq_whisker ((modulePullbackAdjunction B S hS i).homEquiv_unit _ _ _).symm _)

/-- The iterated transpose of the comparison `a^*i^* ⟶ (a ≫ i)^*` of [Stacks Project, Tag 03LU],
followed by the comparison of direct images, is the unit of `(a ≫ i)^* ⊣ (a ≫ i)_*`: it is the
transpose of the comparison composed with its inverse. -/
theorem homEquiv_homEquiv_modulePullbackCompIso_hom_app_comp (a : Z' ⟶ Z) (i : Z ⟶ X)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackAdjunction B S hS i).homEquiv M _
          ((modulePullbackAdjunction B S hS a).homEquiv _ _
            ((modulePullbackCompIso B S hS a i).hom.app M)) ≫
        (modulePushforwardCompIso B S hS a i).hom.app _ =
      (modulePullbackAdjunction B S hS (a ≫ i)).unit.app M := by
  have h₀ := homEquiv_modulePullbackCompIso_inv_app_comp B S hS a i M
    ((modulePullback B S hS (a ≫ i)).obj M) ((modulePullbackCompIso B S hS a i).hom.app M)
  have h₁ : (modulePullbackAdjunction B S hS (a ≫ i)).homEquiv M
      ((modulePullback B S hS (a ≫ i)).obj M)
      ((modulePullbackCompIso B S hS a i).inv.app M ≫
        (modulePullbackCompIso B S hS a i).hom.app M) =
      (modulePullbackAdjunction B S hS (a ≫ i)).unit.app M :=
    (congrArg ((modulePullbackAdjunction B S hS (a ≫ i)).homEquiv M
        ((modulePullback B S hS (a ≫ i)).obj M))
      (Iso.inv_hom_id_app (modulePullbackCompIso B S hS a i) M)).trans
      ((modulePullbackAdjunction B S hS (a ≫ i)).homEquiv_id M)
  exact h₀.symm.trans h₁

/-- **The unit of the composite adjunction, read through the comparison of inverse images.**
The unit of `i^* ⊣ i_*`, followed by the direct image along `i` of the transpose along
`a^* ⊣ a_*` of the comparison `a^*i^* ⟶ (a ≫ i)^*` of [Stacks Project, Tag 03LU] and by the
comparison of direct images, is the unit of `(a ≫ i)^* ⊣ (a ≫ i)_*`. -/
theorem unit_comp_modulePushforward_map_homEquiv_modulePullbackCompIso_hom_app
    (a : Z' ⟶ Z) (i : Z ⟶ X) (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackAdjunction B S hS i).unit.app M ≫
        (modulePushforward B S hS i).map
          ((modulePullbackAdjunction B S hS a).homEquiv ((modulePullback B S hS i).obj M)
            ((modulePullback B S hS (a ≫ i)).obj M)
            ((modulePullbackCompIso B S hS a i).hom.app M)) ≫
        (modulePushforwardCompIso B S hS a i).hom.app ((modulePullback B S hS (a ≫ i)).obj M) =
      (modulePullbackAdjunction B S hS (a ≫ i)).unit.app M :=
  (unit_comp_modulePushforward_map_homEquiv_comp_eq_homEquiv B S hS a i M).trans
    (homEquiv_homEquiv_modulePullbackCompIso_hom_app_comp B S hS a i M)

/-- **The transpose of an inverse image of a transpose, at plain variables.**  Let
`u : I ⟶ i_*M` and `w : J ⟶ (a ≫ i)_*N` be morphisms out of two sheaves of ideals of `𝒪_X`, let
`ψ : a^*M ⟶ N`, and let `incl : I ⟶ J` intertwine `u`, read through the transpose of `ψ`, with
`w`.  Then the inverse image along `a` of the transpose of `u`, followed by `ψ` and read through
`(a ≫ i)^* ≅ a^*i^*`, is the inverse image along `a ≫ i` of `incl` followed by the transpose of
`w`. -/
theorem modulePullbackCompIso_inv_app_comp_map_submoduleTranspose_comp (a : Z' ⟶ Z)
    (i : Z ⟶ X) (I J : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (M : Modules.{u, u} B S hS Z.1 Z.2) (N : Modules.{u, u} B S hS Z'.1 Z'.2)
    (u : I.toSheafOfModules ⟶ (modulePushforward B S hS i).obj M)
    (ψ : (modulePullback B S hS a).obj M ⟶ N)
    (incl : I.toSheafOfModules ⟶ J.toSheafOfModules)
    (w : J.toSheafOfModules ⟶ (modulePushforward B S hS (a ≫ i)).obj N)
    (hw : u ≫ (modulePushforward B S hS i).map
          ((modulePullbackAdjunction B S hS a).homEquiv M N ψ) ≫
        (modulePushforwardCompIso B S hS a i).hom.app N = incl ≫ w) :
    (modulePullbackCompIso B S hS a i).inv.app I.toSheafOfModules ≫
        (modulePullback B S hS a).map (submoduleTranspose B S hS i I M u) ≫ ψ =
      (modulePullback B S hS (a ≫ i)).map incl ≫ submoduleTranspose B S hS (a ≫ i) J N w := by
  apply ((modulePullbackAdjunction B S hS (a ≫ i)).homEquiv I.toSheafOfModules N).injective
  refine (homEquiv_modulePullbackCompIso_inv_app_comp B S hS a i I.toSheafOfModules N
    ((modulePullback B S hS a).map (submoduleTranspose B S hS i I M u) ≫ ψ)).trans ?_
  refine (congrArg (fun m ↦ (modulePullbackAdjunction B S hS i).homEquiv I.toSheafOfModules _ m ≫
      (modulePushforwardCompIso B S hS a i).hom.app N)
    ((modulePullbackAdjunction B S hS a).homEquiv_naturality_left
      (submoduleTranspose B S hS i I M u) ψ)).trans ?_
  refine (congrArg (fun m ↦ m ≫ (modulePushforwardCompIso B S hS a i).hom.app N)
    (((modulePullbackAdjunction B S hS i).homEquiv_naturality_right
        (submoduleTranspose B S hS i I M u)
        ((modulePullbackAdjunction B S hS a).homEquiv M N ψ)).trans
      (eq_whisker (homEquiv_submoduleTranspose B S hS i I M u) _))).trans ?_
  refine ((Category.assoc _ _ _).trans hw).trans ?_
  exact (((modulePullbackAdjunction B S hS (a ≫ i)).homEquiv_naturality_left incl
    (submoduleTranspose B S hS (a ≫ i) J N w)).trans
      (whisker_eq incl (homEquiv_submoduleTranspose B S hS (a ≫ i) J N w))).symm

/-- **A morphism of `𝒪_X`-modules is determined by its underlying morphism of sheaves of
sets.**  Stated at plain variables. -/
theorem eq_of_moduleSheafFunctor_map_eq {M N : Modules.{u, u} B S hS X.1 X.2} {f g : M ⟶ N}
    (h : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map f =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map g) :
    f = g := by
  ext U x
  exact val_app_apply_of_moduleSheafFunctor_map_eq B S hS h U x

/-- **The adjoint first arrow under a change of source.**  For `a : Z' ⟶ Z`, `i : Z ⟶ X` and an
inclusion `incl : 𝓘_i ⟶ 𝓘_{a ≫ i}` of kernel ideal sheaves over `𝒪_X`, the adjoint first arrow
of `i`, followed by the direct image along `i` of the transpose of the comparison
`a^*i^* ⟶ (a ≫ i)^*` and by the comparison of direct images, is `incl` followed by the adjoint
first arrow of `a ≫ i`.

Both are the restriction of `d_{X/Bb}` to `𝓘_i` followed by the unit of
`(a ≫ i)^* ⊣ (a ≫ i)_*`, by
`Space.unit_comp_modulePushforward_map_homEquiv_modulePullbackCompIso_hom_app`. -/
theorem kernelIdealUnitDifferential_comp_modulePushforward_map_homEquiv (a : Z' ⟶ Z)
    (i : Z ⟶ X) (b : X ⟶ Bb)
    (incl : (kernelIdealSheaf B S hS i).toSheafOfModules ⟶
      (kernelIdealSheaf B S hS (a ≫ i)).toSheafOfModules)
    (hincl : incl ≫ (kernelIdealSheaf B S hS (a ≫ i)).ι = (kernelIdealSheaf B S hS i).ι) :
    kernelIdealUnitDifferential B S hS i b ≫
        (modulePushforward B S hS i).map
          ((modulePullbackAdjunction B S hS a).homEquiv _ _
            ((modulePullbackCompIso B S hS a i).hom.app (sheafOfDifferentials B S hS b))) ≫
        (modulePushforwardCompIso B S hS a i).hom.app _ =
      incl ≫ kernelIdealUnitDifferential B S hS (a ≫ i) b := by
  have hT := moduleSheafFunctor_map_kernelIdealUnitDifferential_comp B S hS i b _ _
    ((modulePushforward B S hS i).map
      ((modulePullbackAdjunction B S hS a).homEquiv _ _
        ((modulePullbackCompIso B S hS a i).hom.app (sheafOfDifferentials B S hS b))))
    ((modulePushforwardCompIso B S hS a i).hom.app _)
    (universalDerivationHom B S hS b ≫
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
        ((modulePullbackAdjunction B S hS (a ≫ i)).unit.app (sheafOfDifferentials B S hS b)))
    ((Category.assoc _ _ _).trans (whisker_eq _
      (((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _).symm.trans
        (congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (unit_comp_modulePushforward_map_homEquiv_modulePullbackCompIso_hom_app B S hS a i
            (sheafOfDifferentials B S hS b))))))
  have hR : (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
      (incl ≫ kernelIdealUnitDifferential B S hS (a ≫ i) b) =
      (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          (kernelIdealSheaf B S hS i).ι ≫
        universalDerivationHom B S hS b ≫
          (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
            ((modulePullbackAdjunction B S hS (a ≫ i)).unit.app
              (sheafOfDifferentials B S hS b)) :=
    ((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _).trans
      ((whisker_eq _ (moduleSheafFunctor_map_kernelIdealUnitDifferential B S hS (a ≫ i) b)).trans
        ((Category.assoc _ _ _).symm.trans (eq_whisker
          (((Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map_comp _ _).symm.trans
            (congrArg (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map hincl)) _)))
  exact (Category.assoc _ _ _).symm.trans
    (eq_of_moduleSheafFunctor_map_eq B S hS (hT.trans hR.symm))

/-- `AlgebraicGeometry.Space.kernelConormalFirstMap` is the transpose of the adjoint first arrow;
true by definition, named so that the unfolding is a single step. -/
theorem kernelConormalFirstMap_eq_submoduleTranspose_kernelIdealUnitDifferential (f : Z ⟶ X)
    (b : X ⟶ Bb) :
    kernelConormalFirstMap B S hS f b =
      submoduleTranspose B S hS f (kernelIdealSheaf B S hS f)
        ((modulePullback B S hS f).obj (sheafOfDifferentials B S hS b))
        (kernelIdealUnitDifferential B S hS f b) :=
  rfl

/-- **The first arrow of [Stacks Project, Tag 05ZA] under a change of source.**  For
`a : Z' ⟶ Z`, `i : Z ⟶ X`, `b : X ⟶ Bb` and an inclusion `incl : 𝓘_i ⟶ 𝓘_{a ≫ i}` of kernel
ideal sheaves, the inverse image along `a` of the first arrow `i^*𝓘_i ⟶ i^*Ω_{X/Bb}` of `i`,
read through the comparison `(a ≫ i)^* ≅ a^*i^*` of [Stacks Project, Tag 03LU] on both sides, is
the inverse image along `a ≫ i` of `incl` followed by the first arrow of `a ≫ i`. -/
theorem modulePullbackCompIso_inv_app_comp_map_kernelConormalFirstMap (a : Z' ⟶ Z)
    (i : Z ⟶ X) (b : X ⟶ Bb)
    (incl : (kernelIdealSheaf B S hS i).toSheafOfModules ⟶
      (kernelIdealSheaf B S hS (a ≫ i)).toSheafOfModules)
    (hincl : incl ≫ (kernelIdealSheaf B S hS (a ≫ i)).ι = (kernelIdealSheaf B S hS i).ι) :
    (modulePullbackCompIso B S hS a i).inv.app (kernelIdealSheaf B S hS i).toSheafOfModules ≫
        (modulePullback B S hS a).map (kernelConormalFirstMap B S hS i b) ≫
          (modulePullbackCompIso B S hS a i).hom.app (sheafOfDifferentials B S hS b) =
      (modulePullback B S hS (a ≫ i)).map incl ≫ kernelConormalFirstMap B S hS (a ≫ i) b :=
  (congrArg (fun m ↦ (modulePullbackCompIso B S hS a i).inv.app
      (kernelIdealSheaf B S hS i).toSheafOfModules ≫ (modulePullback B S hS a).map m ≫
        (modulePullbackCompIso B S hS a i).hom.app (sheafOfDifferentials B S hS b))
    (kernelConormalFirstMap_eq_submoduleTranspose_kernelIdealUnitDifferential B S hS i b)).trans <|
  (modulePullbackCompIso_inv_app_comp_map_submoduleTranspose_comp B S hS a i
    (kernelIdealSheaf B S hS i) (kernelIdealSheaf B S hS (a ≫ i))
    ((modulePullback B S hS i).obj (sheafOfDifferentials B S hS b))
    ((modulePullback B S hS (a ≫ i)).obj (sheafOfDifferentials B S hS b))
    (kernelIdealUnitDifferential B S hS i b)
    ((modulePullbackCompIso B S hS a i).hom.app (sheafOfDifferentials B S hS b)) incl
    (kernelIdealUnitDifferential B S hS (a ≫ i) b)
    (kernelIdealUnitDifferential_comp_modulePushforward_map_homEquiv B S hS a i b incl hincl)).trans
    (congrArg (fun m ↦ (modulePullback B S hS (a ≫ i)).map incl ≫ m)
      (kernelConormalFirstMap_eq_submoduleTranspose_kernelIdealUnitDifferential B S hS
        (a ≫ i) b).symm)

/-- `AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_comp_map_kernelConormalFirstMap` at a
morphism `j` equal to `a ≫ i`, the comparison being moved to the other side and a tail `t`
appended. -/
theorem modulePullbackCompIso_hom_app_comp_eqToHom_comp_map_kernelConormalFirstMap
    (a : Z' ⟶ Z) (i : Z ⟶ X) (b : X ⟶ Bb) (j : Z' ⟶ X) (h : a ≫ i = j)
    (incl : (kernelIdealSheaf B S hS i).toSheafOfModules ⟶
      (kernelIdealSheaf B S hS j).toSheafOfModules)
    (hincl : incl ≫ (kernelIdealSheaf B S hS j).ι = (kernelIdealSheaf B S hS i).ι)
    {W : Modules.{u, u} B S hS Z'.1 Z'.2}
    (t : (modulePullback B S hS j).obj (sheafOfDifferentials B S hS b) ⟶ W) :
    (modulePullbackCompIso B S hS a i).hom.app (kernelIdealSheaf B S hS i).toSheafOfModules ≫
        eqToHom (congrArg (fun r : Z' ⟶ X =>
          (modulePullback B S hS r).obj (kernelIdealSheaf B S hS i).toSheafOfModules) h) ≫
        (modulePullback B S hS j).map incl ≫ kernelConormalFirstMap B S hS j b ≫ t =
      (modulePullback B S hS a).map (kernelConormalFirstMap B S hS i b) ≫
        (modulePullbackCompIso B S hS a i).hom.app (sheafOfDifferentials B S hS b) ≫
        eqToHom (congrArg (fun r : Z' ⟶ X =>
          (modulePullback B S hS r).obj (sheafOfDifferentials B S hS b)) h) ≫ t := by
  subst h
  simp only [eqToHom_refl, Category.id_comp]
  exact Iso.hom_comp_comp_comp_eq_of_inv_comp
    ((modulePullbackCompIso B S hS a i).app (kernelIdealSheaf B S hS i).toSheafOfModules) _ _ _ _ t
    (modulePullbackCompIso_inv_app_comp_map_kernelConormalFirstMap B S hS a i b incl hincl)

end SourceChange

/-! ### Naturality of the first arrow along a commutative square of immersions -/

section Square

variable {X X' Z Z' Bb : AlgebraicSpaces B S hS}

/-- **The containment `𝓘_i ⊆ 𝓘_{i' ≫ φ}` of kernel ideal sheaves of a commutative square**
`i' ≫ φ = a ≫ i`, as a morphism of `𝒪_X`-modules: the degree-one part of
`AlgebraicGeometry.Space.kernelIdealZPowCompHom`, read at the kernel ideal sheaves themselves. -/
def kernelIdealSheafSquareHom (i : Z ⟶ X) (i' : Z' ⟶ X') (a : Z' ⟶ Z) (φ : X' ⟶ X)
    (hsq : i' ≫ φ = a ≫ i) :
    (kernelIdealSheaf B S hS i).toSheafOfModules ⟶
      (kernelIdealSheaf B S hS (i' ≫ φ)).toSheafOfModules :=
  eqToHom (congrArg (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule ↦
      K.toSheafOfModules) (kernelIdealSheafZPow_one B S hS i).symm) ≫
    kernelIdealZPowCompHom B S hS i' i a φ hsq 1 ≫
      eqToHom (congrArg (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule ↦
        K.toSheafOfModules) (kernelIdealSheafZPow_one B S hS (i' ≫ φ)))

/-- `AlgebraicGeometry.Space.kernelIdealSheafSquareHom` is an inclusion of sheaves of ideals:
followed by the inclusion of `𝓘_{i' ≫ φ}` into `𝒪_X` it is the inclusion of `𝓘_i`. -/
theorem kernelIdealSheafSquareHom_comp_ι (i : Z ⟶ X) (i' : Z' ⟶ X') (a : Z' ⟶ Z)
    (φ : X' ⟶ X) (hsq : i' ≫ φ = a ≫ i) :
    kernelIdealSheafSquareHom B S hS i i' a φ hsq ≫ (kernelIdealSheaf B S hS (i' ≫ φ)).ι =
      (kernelIdealSheaf B S hS i).ι := by
  rw [kernelIdealSheafSquareHom, Category.assoc, Category.assoc,
    Stacks.SheafOfModules.Submodule.eqToHom_comp_ι (kernelIdealSheafZPow_one B S hS (i' ≫ φ)),
    kernelIdealZPowCompHom_comp_ι,
    Stacks.SheafOfModules.Submodule.eqToHom_comp_ι (kernelIdealSheafZPow_one B S hS i).symm]

/-- **The map `φ^*𝓘_i ⟶ 𝓘_{i'}` of kernel ideal sheaves of a commutative square**
`i' ≫ φ = a ≫ i`: the inverse image along `φ` of the containment `𝓘_i ⊆ 𝓘_{i' ≫ φ}`, followed
by pullback of regular functions along `φ`. -/
def kernelIdealSquarePullbackHom (i : Z ⟶ X) (i' : Z' ⟶ X') (a : Z' ⟶ Z) (φ : X' ⟶ X)
    (hsq : i' ≫ φ = a ≫ i) :
    (modulePullback B S hS φ).obj (kernelIdealSheaf B S hS i).toSheafOfModules ⟶
      (kernelIdealSheaf B S hS i').toSheafOfModules :=
  (modulePullback B S hS φ).map (kernelIdealSheafSquareHom B S hS i i' a φ hsq) ≫
    kernelIdealCompPullbackMap B S hS i' φ

/-- `AlgebraicGeometry.Space.kernelIdealSquarePullbackHom` is pinned by pullback of regular
functions along `φ`. -/
theorem kernelIdealSquarePullbackHom_comp_ι (i : Z ⟶ X) (i' : Z' ⟶ X') (a : Z' ⟶ Z)
    (φ : X' ⟶ X) (hsq : i' ≫ φ = a ≫ i) :
    kernelIdealSquarePullbackHom B S hS i i' a φ hsq ≫ (kernelIdealSheaf B S hS i').ι =
      (modulePullback B S hS φ).map (kernelIdealSheaf B S hS i).ι ≫
        structureModulePullbackMap B S hS φ :=
  (Category.assoc _ _ _).trans ((whisker_eq _ (kernelIdealCompPullbackMap_comp_ι B S hS i' φ)).trans
    ((Category.assoc _ _ _).symm.trans (eq_whisker
      (((modulePullback B S hS φ).map_comp _ _).symm.trans
        (congrArg (modulePullback B S hS φ).map
          (kernelIdealSheafSquareHom_comp_ι B S hS i i' a φ hsq))) _)))

/-- The component of the square comparison `a^*i^* ≅ i'^*φ^*`, with the equality `a ≫ i = i' ≫ φ`
read as an identification of inverse images. -/
private theorem squarePullbackCompIso_hom_app_eq_congrArg (i : Z ⟶ X) (i' : Z' ⟶ X')
    (a : Z' ⟶ Z) (φ : X' ⟶ X) (hsq : i' ≫ φ = a ≫ i)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (squarePullbackCompIso B S hS i' i a φ hsq).hom.app M =
      (modulePullbackCompIso B S hS a i).hom.app M ≫
        eqToHom (congrArg (fun r : Z' ⟶ X => (modulePullback B S hS r).obj M) hsq.symm) ≫
          (modulePullbackCompIso B S hS i' φ).inv.app M :=
  squarePullbackCompIso_hom_app_eqToHom B S hS i' i a φ hsq M _

/-- **The first arrow of [Stacks Project, Tag 05ZA] along a commutative square, at the kernel
ideal sheaves.**  For a commutative square `i' ≫ φ = a ≫ i` and `b : X ⟶ Bb`, the inverse image
along `a` of the first arrow `i^*𝓘_i ⟶ i^*Ω_{X/Bb}` of `i`, followed by the comparison
`a^*i^* ≅ i'^*φ^*` and by `i'^*` of the comparison map `φ^*Ω_{X/Bb} ⟶ Ω_{X'/Bb}`, is the
comparison `a^*i^* ≅ i'^*φ^*` at `𝓘_i`, followed by `i'^*` of the map
`φ^*𝓘_i ⟶ 𝓘_{i'}` and by the first arrow of `i'` over `φ ≫ b`.

The change of source along `a` is
`Space.modulePullbackCompIso_hom_app_comp_eqToHom_comp_map_kernelConormalFirstMap`
and the change of ambient space along `φ` is
`AlgebraicGeometry.Space.kernelConormalFirstMap_compPullbackMap`; no hypothesis on the square or
on `φ` is needed. -/
theorem squarePullbackCompIso_hom_app_comp_map_kernelConormalFirstMap (i : Z ⟶ X)
    (i' : Z' ⟶ X') (a : Z' ⟶ Z) (φ : X' ⟶ X) (hsq : i' ≫ φ = a ≫ i) (b : X ⟶ Bb) :
    (squarePullbackCompIso B S hS i' i a φ hsq).hom.app
          (kernelIdealSheaf B S hS i).toSheafOfModules ≫
        (modulePullback B S hS i').map (kernelIdealSquarePullbackHom B S hS i i' a φ hsq) ≫
          kernelConormalFirstMap B S hS i' (φ ≫ b) =
      (modulePullback B S hS a).map (kernelConormalFirstMap B S hS i b) ≫
        (squarePullbackCompIso B S hS i' i a φ hsq).hom.app (sheafOfDifferentials B S hS b) ≫
          (modulePullback B S hS i').map (pullbackDifferentialsMap B S hS φ b) :=
  comp_comp_eq_of_square_chain _ _ _ _
    (squarePullbackCompIso_hom_app_eq_congrArg B S hS i i' a φ hsq _) _ _ _
    ((modulePullback B S hS i').map_comp _ _) _ _ _
    ((modulePullbackCompIso B S hS i' φ).inv.naturality
      (kernelIdealSheafSquareHom B S hS i i' a φ hsq)).symm _ _ _
    (kernelConormalFirstMap_compPullbackMap B S hS i' φ b (φ ≫ b)
      (isSheafOfDifferentialsMap_pullbackDifferentialsMap B S hS φ b)) _ _ _ _
    (squarePullbackCompIso_hom_app_eq_congrArg B S hS i i' a φ hsq _)
    (modulePullbackCompIso_hom_app_comp_eqToHom_comp_map_kernelConormalFirstMap B S hS a i b
      (i' ≫ φ) hsq.symm _ (kernelIdealSheafSquareHom_comp_ι B S hS i i' a φ hsq) _)

/-- **The identification of the conormal module with `i^*𝓘_i`, at the
`AlgebraicGeometry.Space.kernelIdealSheafZPow` spelling**: the inverse of the bridge
`AlgebraicGeometry.Space.conormalModuleOfImmersionZPowIso` followed by the transport along
`AlgebraicGeometry.Space.kernelIdealSheafZPow_one`.  True by definition, as an equation of
isomorphisms; the respelling of the degree-one piece of the conormal algebra is paid for here,
once. -/
theorem conormalModuleOfImmersionKernelPullbackIso_eq_zPowIso (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) :
    conormalModuleOfImmersionKernelPullbackIso B S hS i hi =
      (conormalModuleOfImmersionZPowIso B S hS i hi).symm ≪≫
        eqToIso (congrArg
          (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
            (modulePullback B S hS i).obj N.toSheafOfModules)
          (kernelIdealSheafZPow_one B S hS i)) :=
  rfl

/-- `AlgebraicGeometry.Space.conormalModuleOfImmersionKernelPullbackIso_eq_zPowIso` on the
forward morphisms. -/
theorem conormalModuleOfImmersionKernelPullbackIso_hom_eq (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) :
    (conormalModuleOfImmersionKernelPullbackIso B S hS i hi).hom =
      (conormalModuleOfImmersionZPowIso B S hS i hi).inv ≫
        eqToHom (congrArg
            (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
              (modulePullback B S hS i).obj N.toSheafOfModules)
            (kernelIdealSheafZPow_one B S hS i)) :=
  (congrArg Iso.hom (conormalModuleOfImmersionKernelPullbackIso_eq_zPowIso B S hS i hi)).trans
    (Iso.symm_trans_eqToIso_hom (conormalModuleOfImmersionZPowIso B S hS i hi) _)

/-- `AlgebraicGeometry.Space.conormalModuleOfImmersionKernelPullbackIso_eq_zPowIso` on the
inverse morphisms. -/
theorem conormalModuleOfImmersionKernelPullbackIso_inv_eq (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) :
    (conormalModuleOfImmersionKernelPullbackIso B S hS i hi).inv =
      eqToHom (congrArg
          (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
            (modulePullback B S hS i).obj N.toSheafOfModules)
          (kernelIdealSheafZPow_one B S hS i)).symm ≫
        (conormalModuleOfImmersionZPowIso B S hS i hi).hom :=
  (congrArg Iso.inv (conormalModuleOfImmersionKernelPullbackIso_eq_zPowIso B S hS i hi)).trans
    (Iso.symm_trans_eqToIso_inv (conormalModuleOfImmersionZPowIso B S hS i hi) _)

/-- **The canonical map of [Stacks Project, Tag 04CP], read at the kernel ideal sheaves.**  For a
commutative square `i' ≫ φ = a ≫ i` of immersions, the canonical map
`a^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}`, conjugated by the identifications
`AlgebraicGeometry.Space.conormalModuleOfImmersionKernelPullbackIso` of the two conormal modules
with the inverse images of the kernel ideal sheaves, is the comparison `a^*i^* ≅ i'^*φ^*` at
`𝓘_i` followed by `i'^*` of `AlgebraicGeometry.Space.kernelIdealSquarePullbackHom`.

The two maps `φ^*𝓘_i ⟶ 𝓘_{i'}` of ideal sheaves involved — this one and the degree-one part of
`AlgebraicGeometry.Space.kernelIdealSquareMap` — are pinned by the same composite with the
inclusion of `𝓘_{i'}` into `𝒪_{X'}`, which is a monomorphism. -/
theorem conormalMapOfImmersions_eq_kernelIdeal (i : Z ⟶ X) (i' : Z' ⟶ X') (a : Z' ⟶ Z)
    (φ : X' ⟶ X) (hi : IsImmersion B S hS i.hom) (hi' : IsImmersion B S hS i'.hom)
    (hsq : i' ≫ φ = a ≫ i) :
    conormalMapOfImmersions B S hS i' i a φ hi' hi hsq =
      (modulePullback B S hS a).map (conormalModuleOfImmersionKernelPullbackIso B S hS i hi).hom ≫
        (squarePullbackCompIso B S hS i' i a φ hsq).hom.app
            (kernelIdealSheaf B S hS i).toSheafOfModules ≫
          (modulePullback B S hS i').map (kernelIdealSquarePullbackHom B S hS i i' a φ hsq) ≫
            (conormalModuleOfImmersionKernelPullbackIso B S hS i' hi').inv := by
  have hmono : Mono (kernelIdealSheafZPow B S hS i' 1).ι := inferInstance
  have hm := CategoryTheory.eq_eqToHom_comp_comp_eqToHom_of_mono (modulePullback B S hS φ)
    (Stacks.SheafOfModules.Submodule.eqToHom_comp_ι (kernelIdealSheafZPow_one B S hS i)
      (congrArg (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule ↦
        K.toSheafOfModules) (kernelIdealSheafZPow_one B S hS i)))
    (Stacks.SheafOfModules.Submodule.eqToHom_comp_ι (kernelIdealSheafZPow_one B S hS i').symm
      (congrArg (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X')).Submodule ↦
        K.toSheafOfModules) (kernelIdealSheafZPow_one B S hS i').symm))
    hmono (kernelIdealSquareMap_comp_ι B S hS i' i a φ hsq 1)
    (kernelIdealSquarePullbackHom_comp_ι B S hS i i' a φ hsq)
  have hG := CategoryTheory.map_eqToHom_comp_app_comp_map_comp_eqToHom
    (modulePullback B S hS i) (modulePullback B S hS a) (modulePullback B S hS φ)
    (modulePullback B S hS i') (squarePullbackCompIso B S hS i' i a φ hsq)
    (congrArg (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule ↦
      K.toSheafOfModules) (kernelIdealSheafZPow_one B S hS i))
    (congrArg (fun K : (SheafOfModules.unit (structureRingSheaf B S hS X')).Submodule ↦
      K.toSheafOfModules) (kernelIdealSheafZPow_one B S hS i').symm)
    _ _ hm
    (congrArg
      (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
        (modulePullback B S hS i).obj N.toSheafOfModules)
      (kernelIdealSheafZPow_one B S hS i)).symm
    (congrArg
      (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X')).Submodule =>
        (modulePullback B S hS i').obj N.toSheafOfModules)
      (kernelIdealSheafZPow_one B S hS i'))
  refine (conormalMapOfImmersions_eq_kernelIdealZPowSquareMap B S hS i' i a φ hi' hi hsq).trans ?_
  refine (Functor.map_comp_comp_comp_eq_of_eqToHom (modulePullback B S hS a)
    (conormalModuleOfImmersionZPowIso B S hS i hi).inv
    (eqToHom (congrArg
      (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
        (modulePullback B S hS i).obj N.toSheafOfModules)
      (kernelIdealSheafZPow_one B S hS i)))
    (eqToHom (congrArg
      (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule =>
        (modulePullback B S hS i).obj N.toSheafOfModules)
      (kernelIdealSheafZPow_one B S hS i)).symm)
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _)) _ _ _ _
    (eqToHom (congrArg
      (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X')).Submodule =>
        (modulePullback B S hS i').obj N.toSheafOfModules)
      (kernelIdealSheafZPow_one B S hS i')))
    (eqToHom (congrArg
      (fun N : (SheafOfModules.unit (structureRingSheaf B S hS X')).Submodule =>
        (modulePullback B S hS i').obj N.toSheafOfModules)
      (kernelIdealSheafZPow_one B S hS i')).symm)
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
    (conormalModuleOfImmersionZPowIso B S hS i' hi').hom hG).trans ?_
  rw [conormalModuleOfImmersionKernelPullbackIso_hom_eq,
    conormalModuleOfImmersionKernelPullbackIso_inv_eq]

/-- **Naturality of the first arrow of [Stacks Project, Tag 05ZA] along a commutative square of
immersions.**  For a commutative square `i' ≫ φ = a ≫ i` of immersions and `b : X ⟶ Bb`, the
canonical map `a^*𝒞_{Z/X} ⟶ 𝒞_{Z'/X'}` of [Stacks Project, Tag 04CP] followed by the first arrow
`𝒞_{Z'/X'} ⟶ i'^*Ω_{X'/Bb}` of `i'` over `φ ≫ b` is the inverse image along `a` of the first arrow
`𝒞_{Z/X} ⟶ i^*Ω_{X/Bb}` of `i`, followed by the comparison `a^*i^* ≅ i'^*φ^*` and by `i'^*` of
the comparison map `φ^*Ω_{X/Bb} ⟶ Ω_{X'/Bb}` of [Stacks Project, Tag 04CX]. -/
theorem conormalMapOfImmersions_comp_conormalSequenceFirstMapOfImmersion (i : Z ⟶ X)
    (i' : Z' ⟶ X') (a : Z' ⟶ Z) (φ : X' ⟶ X) (hi : IsImmersion B S hS i.hom)
    (hi' : IsImmersion B S hS i'.hom) (hsq : i' ≫ φ = a ≫ i) (b : X ⟶ Bb) :
    conormalMapOfImmersions B S hS i' i a φ hi' hi hsq ≫
        conormalSequenceFirstMapOfImmersion B S hS i' hi' (φ ≫ b) =
      (modulePullback B S hS a).map (conormalSequenceFirstMapOfImmersion B S hS i hi b) ≫
        (squarePullbackCompIso B S hS i' i a φ hsq).hom.app (sheafOfDifferentials B S hS b) ≫
          (modulePullback B S hS i').map (pullbackDifferentialsMap B S hS φ b) := by
  rw [conormalMapOfImmersions_eq_kernelIdeal, conormalSequenceFirstMapOfImmersion,
    conormalSequenceFirstMapOfImmersion, Functor.map_comp, Category.assoc, Category.assoc,
    Category.assoc, Iso.inv_hom_id_assoc,
    squarePullbackCompIso_hom_app_comp_map_kernelConormalFirstMap]
  exact (Category.assoc _ _ _).symm

end Square

/-! ### Stacks 05ZB, the étale-local clause -/

section EtaleLocal

variable {X X' Z Z' Bb : AlgebraicSpaces B S hS}

/-- **The restriction of the conormal sequence along one étale chart is split exact.**  Let
`i : Z ⟶ X` be an immersion of algebraic spaces over `Bb` with structure morphism `b : X ⟶ Bb`,
let `φ : X' ⟶ X` be étale, let
```
Z' --i'--→ X'
|          |
a          φ
↓          ↓
Z  --i---→ X
```
be cartesian, and let `g : X' ⟶ Z'` be a left inverse of `i'` over `Bb`.  Then the inverse
image along `a` of the conormal sequence of [Stacks Project, Tag 05ZA] of `i`, the whole short
complex
```
  a^*𝒞_{Z/X} ⟶ a^*i^*Ω_{X/Bb} ⟶ a^*Ω_{Z/Bb},
```
admits a `CategoryTheory.ShortComplex.Splitting`.

It is isomorphic to the sequence of `i'` over `φ ≫ b`, which is split by
`AlgebraicGeometry.Space.nonempty_conormalSequenceOfImmersion_splitting`: on the conormal terms
by the canonical map of [Stacks Project, Tag 04CP], invertible by [Stacks Project, Tag 04CO]; on
the middle and right-hand terms by the comparison maps of [Stacks Project, Tag 04CU]. -/
@[sga "6 VIII 2.2" "partial"]
theorem nonempty_map_conormalSequenceOfImmersion_splitting_of_isPullback (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) (b : X ⟶ Bb) (φ : X' ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (i' : Z' ⟶ X') (a : Z' ⟶ Z) (hpb : IsPullback i' a φ i) (g : X' ⟶ Z')
    (hg : i' ≫ g = 𝟙 Z') (hgb : g ≫ i' ≫ φ ≫ b = φ ≫ b) :
    Nonempty ((ShortComplex.mk _ _
      (conormalSequenceFirstMapOfImmersion_comp_pullbackDifferentialsMap_eq_zero
        B S hS i hi b)).map (modulePullback B S hS a)).Splitting := by
  have hi' : IsImmersion B S hS i'.hom := isImmersion_of_isPullback B S hS hpb.flip hi
  have ha : IsEtale B S hS a.hom := isEtale_of_isPullback B S hS i' a φ i hpb hφ
  have hsq : i' ≫ φ = a ≫ i := hpb.w
  have hpath : a ≫ i ≫ b = i' ≫ φ ≫ b := by
    rw [← Category.assoc, ← hsq, Category.assoc]
  have hpath' : a ≫ i ≫ b = (i' ≫ φ ≫ b) ≫ 𝟙 Bb := hpath.trans (Category.comp_id _).symm
  have hsp := nonempty_conormalSequenceOfImmersion_splitting B S hS i' hi' (φ ≫ b) g hg hgb
  have hL : IsIso (conormalMapOfImmersions B S hS i' i a φ hi' hi hsq) :=
    isIso_conormalMapOfImmersions_of_isPullback_of_isEtale B S hS i' i hi' hi a φ hpb.flip hφ
  have hM : IsIso (pullbackDifferentialsMap B S hS φ b) :=
    isIso_pullbackDifferentialsMap_of_isEtale B S hS φ hφ b
  have hca := isSheafOfDifferentialsMap_sheafOfDifferentialsMap B S hS a (i ≫ b)
    (i' ≫ φ ≫ b) (𝟙 Bb) hpath'
  have hR : IsIso (sheafOfDifferentialsMap B S hS a (i ≫ b) (i' ≫ φ ≫ b) (𝟙 Bb) hpath') :=
    isIso_of_isSheafOfDifferentialsMap_etale B S hS a ha (i ≫ b) (i' ≫ φ ≫ b) hpath hca
  have hsecond := comp_comp_eq_eqToHom_comp B S hS i b φ i' a hsq _ hca
  refine ⟨hsp.some.ofIso (Iso.symm ?_)⟩
  refine ShortComplex.isoMk (asIso (conormalMapOfImmersions B S hS i' i a φ hi' hi hsq))
    ((squarePullbackCompIso B S hS i' i a φ hsq).app (sheafOfDifferentials B S hS b) ≪≫
      (modulePullback B S hS i').mapIso (asIso (pullbackDifferentialsMap B S hS φ b)))
    (asIso (sheafOfDifferentialsMap B S hS a (i ≫ b) (i' ≫ φ ≫ b) (𝟙 Bb) hpath')) ?_ ?_
  · exact conormalMapOfImmersions_comp_conormalSequenceFirstMapOfImmersion B S hS i i' a φ hi
      hi' hsq b
  · show ((squarePullbackCompIso B S hS i' i a φ hsq).hom.app (sheafOfDifferentials B S hS b) ≫
        (modulePullback B S hS i').map (pullbackDifferentialsMap B S hS φ b)) ≫
          pullbackDifferentialsMap B S hS i' (φ ≫ b) =
      (modulePullback B S hS a).map (pullbackDifferentialsMap B S hS i b) ≫
        sheafOfDifferentialsMap B S hS a (i ≫ b) (i' ≫ φ ≫ b) (𝟙 Bb) hpath'
    exact Iso.comp_comp_eq_of_hom_comp
      ((modulePullbackCompIso B S hS a i).app (sheafOfDifferentials B S hS b)) _ _ _
      (squarePullbackCompIso_hom_app_eq_congrArg B S hS i i' a φ hsq _) _ _ _ _ hsecond

/-- **Stacks 05ZB, the étale-local clause in full.**  Let `i : Z ⟶ X` be an immersion of
algebraic spaces over `Bb` with structure morphism `b : X ⟶ Bb`, and assume that `i` étale
locally has a left inverse: there is an étale covering `{φ_k : X_k ⟶ X}` of `X`
(Stacks 041E: every `φ_k` étale, the family jointly surjective) such that, for each `k`, in a
cartesian square
```
Z_k --i_k--→ X_k
 |            |
a_k          φ_k
 ↓            ↓
 Z  ---i---→  X
```
presenting `Z_k` as `Z ×_X X_k`, the immersion `i_k` has a left inverse `g_k` over `Bb`.  Then
for every `k` the restriction to `Z_k` of the conormal sequence of [Stacks Project, Tag 05ZA]
of `i` — the image under `a_k^*` of the whole short complex
```
  𝒞_{Z/X} ⟶ i^*Ω_{X/Bb} ⟶ Ω_{Z/Bb},
```
conormal term and first arrow included — admits a `CategoryTheory.ShortComplex.Splitting`.  So
the restricted first arrow `a_k^*𝒞_{Z/X} ⟶ a_k^*i^*Ω_{X/Bb}` is a monomorphism, the restricted
sequence is exact at its middle term, and its second arrow is a split epimorphism.

Each member is
`AlgebraicGeometry.Space.nonempty_map_conormalSequenceOfImmersion_splitting_of_isPullback`. -/
@[stacks 05ZB "the étale-local clause in full: if i étale locally has a left inverse (on an \
étale covering {X_k → X} with Z_k = Z ×_X X_k), the restriction to each Z_k of the whole \
conormal sequence of i is split exact"]
theorem nonempty_map_conormalSequenceOfImmersion_splitting_of_isEtaleCovering (i : Z ⟶ X)
    (hi : IsImmersion B S hS i.hom) (b : X ⟶ Bb) {ι : Type*}
    {Xk Zk : ι → AlgebraicSpaces B S hS} (φ : ∀ k, Xk k ⟶ X)
    (hφ : IsEtaleCovering B S hS (fun k ↦ (Xk k).1) (fun k ↦ (φ k).hom))
    (ik : ∀ k, Zk k ⟶ Xk k) (a : ∀ k, Zk k ⟶ Z) (hpb : ∀ k, IsPullback (ik k) (a k) (φ k) i)
    (g : ∀ k, Xk k ⟶ Zk k) (hg : ∀ k, ik k ≫ g k = 𝟙 (Zk k))
    (hgb : ∀ k, g k ≫ ik k ≫ φ k ≫ b = φ k ≫ b) (k : ι) :
    Nonempty ((ShortComplex.mk _ _
      (conormalSequenceFirstMapOfImmersion_comp_pullbackDifferentialsMap_eq_zero
        B S hS i hi b)).map (modulePullback B S hS (a k))).Splitting :=
  nonempty_map_conormalSequenceOfImmersion_splitting_of_isPullback B S hS i hi b (φ k)
    (hφ.etale k) (ik k) (a k) (hpb k) (g k) (hg k) (hgb k)

end EtaleLocal

end AlgebraicGeometry.Space

end

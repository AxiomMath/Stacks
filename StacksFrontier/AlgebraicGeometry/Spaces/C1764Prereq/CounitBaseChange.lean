module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Adjunction.LeftAdjointUniqPasting
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingModulesFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# The pullback of the counit `f^*f_* ⟶ 𝟭` along a commutative square

Let `g' ≫ f = f' ≫ g` be a commutative square of algebraic spaces, with `f : X ⟶ Y`,
`g : Y' ⟶ Y`, `f' : X' ⟶ Y'` and `g' : X' ⟶ X`. For a module `K` on `X`, the pullback along `g'`
of the counit `f^*f_*K ⟶ K` of the adjunction of Stacks 03LU factors as

`(g')^*f^*f_*K ≅ (f')^*g^*f_*K ⟶ (f')^*f'_*(g')^*K ⟶ (g')^*K`,

the comparison of the two composite inverse images, then `(f')^*` of the base change map
`g^*f_*K ⟶ f'_*(g')^*K` of `AlgebraicGeometry.Space.moduleBaseChangeMap`, then the counit of `f'`.
This is a formal statement about mates, proved first for abstract adjunctions.

## Main results

* `AlgebraicGeometry.C1764Prereq.map_counit_eq_comp_mateEquiv_symm`: the abstract factorization.
* `AlgebraicGeometry.C1764Prereq.modulePullback_map_counit_eq`: the factorization for modules on
  algebraic spaces.
* `AlgebraicGeometry.C1764Prereq.epi_modulePullback_map_counit`: if the base change map and the
  counit of `f'` are surjective, so is the pullback of the counit of `f`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 073K](https://stacks.math.columbia.edu/tag/073K)
* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.C1764Prereq

section Abstract

variable {A : Type*} {B : Type*} {A' : Type*} {B' : Type*}
  [Category* A] [Category* B] [Category* A'] [Category* B']
  {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
  {Lg : A ⥤ A'} {Rg : A' ⥤ A} {Lg' : B ⥤ B'} {Rg' : B' ⥤ B} {ι : Type*}
  {Lk : ι → (A ⥤ B')} {Rk : ι → (B' ⥤ A)}

/-- **The pulled back counit factors through the base change map.** For a square of adjunctions
`Lf ⊣ Rf`, `Lf' ⊣ Rf'` (vertical) and `Lg ⊣ Rg`, `Lg' ⊣ Rg'` (horizontal) whose two composite
left adjoints `ef`, `eg` are identified with a common one by uniqueness of adjoints, `Lg'` of the
counit of `Lf ⊣ Rf` is the comparison `E` of the two composites, followed by `Lf'` of the base
change map `β` (the horizontal mate of the comparison of composite right adjoints), followed by
the counit of `Lf' ⊣ Rf'`. -/
theorem map_counit_eq_comp_mateEquiv_symm (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf')
    (adjg : Lg ⊣ Rg) (adjg' : Lg' ⊣ Rg') (ak : ∀ k, Lk k ⊣ Rk k) {k₁ k₂ : ι} (hk : k₁ = k₂)
    (P : Rf' ⋙ Rg ≅ Rk k₂) (Q : Rg' ⋙ Rf ≅ Rk k₁)
    (ef : Lf ⋙ Lg' ≅ Lk k₁)
    (hef : ef = Adjunction.leftAdjointUniq ((adjf.comp adjg').ofNatIsoRight Q) (ak k₁))
    (eg : Lg ⋙ Lf' ≅ Lk k₂)
    (heg : eg = Adjunction.leftAdjointUniq ((adjg.comp adjf').ofNatIsoRight P) (ak k₂))
    (E : Lf ⋙ Lg' ≅ Lg ⋙ Lf') (hE : E = ef ≪≫ eqToIso (congrArg Lk hk) ≪≫ eg.symm)
    (β : Rf ⋙ Lg ⟶ Lg' ⋙ Rf')
    (hβ : β = (mateEquiv adjg' adjg).symm
      (TwoSquare.mk _ _ _ _ (Q.hom ≫ eqToHom (congrArg Rk hk) ≫ P.inv))) (K : B) :
    Lg'.map (adjf.counit.app K) =
      E.hom.app (Rf.obj K) ≫ Lf'.map (β.app K) ≫ adjf'.counit.app (Lg'.obj K) := by
  subst hk hef heg hE hβ
  set eg := Adjunction.leftAdjointUniq ((adjg.comp adjf').ofNatIsoRight P) (ak k₁)
  set ef := Adjunction.leftAdjointUniq ((adjf.comp adjg').ofNatIsoRight Q) (ak k₁)
  have hg : conjugateEquiv (ak k₁) (adjg.comp adjf') eg.hom = P.inv := by
    have h := Stacks.CategoryTheory.LeftAdjointUniqPasting.conjugateEquiv_leftAdjointUniq_inv
      (ak k₁) (adjg.comp adjf') P
    refine Eq.trans ?_ h
    congr 1
  have hf : conjugateEquiv (adjf.comp adjg') (ak k₁) ef.inv = Q.hom := by
    have h := Stacks.CategoryTheory.LeftAdjointUniqPasting.conjugateEquiv_leftAdjointUniq_hom
      (ak k₁) (adjf.comp adjg') Q
    refine Eq.trans ?_ h
    congr 1
  have h₁ := Stacks.CategoryTheory.LeftAdjointUniqPasting.twoSquare_eq_mateEquiv_symm adjf adjf'
    adjg adjg' (ak k₁) eg ef P Q hg hf
  have h₂ := Stacks.CategoryTheory.BaseChange.homEquiv_symm_map adjf adjf' eg ef K
  rw [Adjunction.homEquiv_counit] at h₂
  simp only [Stacks.CategoryTheory.BaseChange.map, h₁] at h₂
  simp only [eqToHom_refl, Category.id_comp, eqToIso_refl, Iso.refl_trans, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [h₂]
  simp

end Abstract

section Spaces

open Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y X' Y' : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (comm : g' ≫ f = f' ≫ g)

/-- **The pullback of the counit `f^*f_*K ⟶ K` along a commutative square of algebraic spaces**
is the comparison `(g')^*f^* ≅ (f')^*g^*`, followed by `(f')^*` of the base change map
`g^*f_*K ⟶ f'_*(g')^*K`, followed by the counit of `f'` at `(g')^*K`. -/
theorem modulePullback_map_counit_eq (K : Space.Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS g').map ((modulePullbackAdjunction B S hS f).counit.app K) =
      (modulePullbackSquareComparison f g f' g' comm).hom.app
          ((modulePushforward B S hS f).obj K) ≫
        (modulePullback B S hS f').map ((moduleBaseChangeMap f g f' g' comm).app K) ≫
        (modulePullbackAdjunction B S hS f').counit.app ((modulePullback B S hS g').obj K) :=
  map_counit_eq_comp_mateEquiv_symm (modulePullbackAdjunction B S hS f)
    (modulePullbackAdjunction B S hS f') (modulePullbackAdjunction B S hS g)
    (modulePullbackAdjunction B S hS g') (fun k : X' ⟶ Y => modulePullbackAdjunction B S hS k)
    comm (modulePushforwardCompIso B S hS f' g) (modulePushforwardCompIso B S hS g' f)
    (modulePullbackCompIso B S hS g' f) (modulePullbackCompIso.eq_1 B S hS g' f)
    (modulePullbackCompIso B S hS f' g) (modulePullbackCompIso.eq_1 B S hS f' g)
    (modulePullbackSquareComparison f g f' g' comm)
    (modulePullbackSquareComparison.eq_1 f g f' g' comm)
    (moduleBaseChangeMap f g f' g' comm) (moduleBaseChangeMap.eq_1 f g f' g' comm) K

/-- **Surjectivity of the pulled back counit from surjectivity of the base change map.** If the
base change map `g^*f_*K ⟶ f'_*(g')^*K` and the counit of `f'` at `(g')^*K` are surjective, then
so is the pullback along `g'` of the counit `f^*f_*K ⟶ K`. -/
theorem epi_modulePullback_map_counit (K : Space.Modules.{u, u} B S hS X.1 X.2)
    (hβ : Epi ((moduleBaseChangeMap f g f' g' comm).app K))
    (hε : Epi ((modulePullbackAdjunction B S hS f').counit.app
      ((modulePullback B S hS g').obj K))) :
    Epi ((modulePullback B S hS g').map ((modulePullbackAdjunction B S hS f).counit.app K)) := by
  have : (modulePullback B S hS f').PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS f')
  rw [modulePullback_map_counit_eq f g f' g' comm K]
  infer_instance

end Spaces

end AlgebraicGeometry.C1764Prereq

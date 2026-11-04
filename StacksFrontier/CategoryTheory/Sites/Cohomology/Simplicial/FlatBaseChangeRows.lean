module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FlatBaseChangeAssembly
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings

/-!
# The row filtration on the base-changed side of the Δ-instance of Stacks 08RX

Let `φ : O ⟶ O'` be a map of simplicial commutative rings. A quasi-isomorphism of bounded above
complexes of simplicial `O`-modules which are sectionwise flat stays a quasi-isomorphism on the
total complexes of the double complexes obtained by applying base change along `φ` and taking
Moore complexes. With the resolution of a simplicial module by standard covers this gives the
Δ-instance of [Stacks, Tag 08RX].

The row `q = -n` of the base-changed double complex is the complex of simplicial modules
evaluated at the object `⦋n⦌` of `Δ` and then tensored with `O'_n` over `O_n`
(`Stacks.SimplicialModules.baseChangedMooreCochainCompEvalIso`), read on underlying abelian
groups. A bounded above complex of flat modules is K-flat (`CochainComplex.KFlat.kFlat_of_flat`,
[Stacks, Tag 064K]), and extension of scalars preserves quasi-isomorphisms between K-flat
complexes (`CochainComplex.DerivedTensor.KFlatDerived.quasiIso_extendScalars_map_of_kFlat`).

## Main definitions

* `CategoryTheory.Functor.mapHomologicalComplexIso`: naturally isomorphic functors preserving zero
  morphisms induce isomorphic functors on homological complexes.
* `Stacks.SimplicialModules.baseChangedMooreCochainCompEvalIso`: the row `q = -n` of the
  base-changed double complex, identified with evaluation at `⦋n⦌` followed by extension of
  scalars.

## Main results

* `Stacks.SimplicialModules.quasiIso_eval_extendScalars_map`: the flat base-change step in one
  simplicial degree.
* `Stacks.SimplicialModules.quasiIso_total_map_baseChangedMooreBicomplex`: the row filtration
  on the base-changed side.
* `Stacks.SimplicialModules.quasiIso_mooreCochainBaseChange_app`: the Δ-instance of
  [Stacks, Tag 08RX].

## References

* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
* [Stacks Project, Tag 064K](https://stacks.math.columbia.edu/tag/064K)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open StacksDraft.TotalComplexQuasiIso

universe u

namespace CategoryTheory.Functor

/-- Naturally isomorphic functors preserving zero morphisms induce isomorphic functors on
homological complexes. -/
def mapHomologicalComplexIso {V W : Type*} [Category* V] [Category* W] [Preadditive V]
    [Preadditive W] {ι : Type*} (c : ComplexShape ι) {F G : V ⥤ W} [F.PreservesZeroMorphisms]
    [G.PreservesZeroMorphisms] (e : F ≅ G) :
    F.mapHomologicalComplex c ≅ G.mapHomologicalComplex c :=
  NatIso.ofComponents
    (fun K => HomologicalComplex.Hom.isoOfComponents (fun i => e.app (K.X i))
      (fun i j _ => (e.hom.naturality (K.d i j)).symm))
    (fun f => by ext i; exact e.hom.naturality (f.f i))

end CategoryTheory.Functor

namespace Stacks.SimplicialModules

open Stacks.PresheafOfModules.ChangeOfRings

variable {O O' : SimplexCategoryᵒᵖ ⥤ CommRingCat.{u}} (φ : O ⟶ O')

/-- **The row `q = -n` of the base-changed double complex**: evaluation at the object `⦋n⦌` of
`Δ`, followed by extension of scalars along `φ_n : O_n ⟶ O'_n` and the forgetful functor to
abelian groups. -/
def baseChangedMooreCochainCompEvalIso (n : ℕ) :
    (changeOfRings φ ⋙ mooreCochain O') ⋙
        HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ)
          ((ComplexShape.embeddingUpIntLE (0 : ℤ)).f n) ≅
      PresheafOfModules.evaluation (ringPresheaf O) (op (SimplexCategory.mk n)) ⋙
        ModuleCat.extendScalars (φ.app (op (SimplexCategory.mk n))).hom ⋙
          forget₂ (ModuleCat.{u} ↥(O'.obj (op (SimplexCategory.mk n)))) AddCommGrpCat.{u} :=
  Functor.isoWhiskerLeft (changeOfRings φ ⋙
      PresheafOfModules.toPresheaf (ringPresheaf O'))
    (alternatingFaceMapCochainComplexCompEvalIso AddCommGrpCat.{u} n)

/-- **The flat base-change step in one simplicial degree.** A quasi-isomorphism of complexes of
simplicial modules, both bounded above by `0` and both sectionwise flat in the degree `⦋n⦌`,
stays a quasi-isomorphism after evaluation at `⦋n⦌` and extension of scalars along `φ_n`. -/
theorem quasiIso_eval_extendScalars_map (n : ℕ)
    {K L : CochainComplex (SMod O) ℤ} (f : K ⟶ L) [QuasiIso f]
    [CochainComplex.IsStrictlyLE K 0] [CochainComplex.IsStrictlyLE L 0]
    (hK : ∀ p : ℤ, Module.Flat ↥((ringPresheaf O).obj (op (SimplexCategory.mk n)))
      ↥((K.X p).obj (op (SimplexCategory.mk n))))
    (hL : ∀ p : ℤ, Module.Flat ↥((ringPresheaf O).obj (op (SimplexCategory.mk n)))
      ↥((L.X p).obj (op (SimplexCategory.mk n)))) :
    QuasiIso (((PresheafOfModules.evaluation (ringPresheaf O) (op (SimplexCategory.mk n)) ⋙
      ModuleCat.extendScalars (φ.app (op (SimplexCategory.mk n))).hom ⋙
        forget₂ (ModuleCat.{u} ↥(O'.obj (op (SimplexCategory.mk n))))
          AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have hkf : ∀ J : CochainComplex (SMod O) ℤ, J.IsStrictlyLE 0 →
      (∀ p : ℤ, Module.Flat ↥((ringPresheaf O).obj (op (SimplexCategory.mk n)))
        ↥((J.X p).obj (op (SimplexCategory.mk n)))) →
      CochainComplex.KFlat
        (((PresheafOfModules.evaluation (ringPresheaf O)
          (op (SimplexCategory.mk n))).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    fun J _ hJ => by
      have hJi : ∀ p : ℤ, Module.Flat ↥((ringPresheaf O).obj (op (SimplexCategory.mk n)))
          ↥((((PresheafOfModules.evaluation (ringPresheaf O)
            (op (SimplexCategory.mk n))).mapHomologicalComplex (ComplexShape.up ℤ)).obj J).X p) :=
        hJ
      exact CochainComplex.KFlat.kFlat_of_flat _ 0
  have hev : QuasiIso (((PresheafOfModules.evaluation (ringPresheaf O)
      (op (SimplexCategory.mk n))).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    HomologicalComplex.quasiIso_map_of_preservesHomology f _
  have hext := CochainComplex.DerivedTensor.KFlatDerived.quasiIso_extendScalars_map_of_kFlat
    (φ.app (op (SimplexCategory.mk n))).hom
    (((PresheafOfModules.evaluation (ringPresheaf O)
      (op (SimplexCategory.mk n))).mapHomologicalComplex (ComplexShape.up ℤ)).map f)
    (hkf K inferInstance hK) (hkf L inferInstance hL)
  have hext' : QuasiIso
      (((ModuleCat.extendScalars (φ.app (op (SimplexCategory.mk n))).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).map
          (((PresheafOfModules.evaluation (ringPresheaf O)
            (op (SimplexCategory.mk n))).mapHomologicalComplex (ComplexShape.up ℤ)).map f)) :=
    hext
  exact HomologicalComplex.quasiIso_map_of_preservesHomology
    (((ModuleCat.extendScalars (φ.app (op (SimplexCategory.mk n))).hom).mapHomologicalComplex
      (ComplexShape.up ℤ)).map
        (((PresheafOfModules.evaluation (ringPresheaf O)
          (op (SimplexCategory.mk n))).mapHomologicalComplex (ComplexShape.up ℤ)).map f))
    (forget₂ (ModuleCat.{u} ↥(O'.obj (op (SimplexCategory.mk n)))) AddCommGrpCat.{u})

/-! ### Flatness of the sections of the resolution -/

/-- A simplicial module which is zero or isomorphic to a standard cover has flat sections. -/
lemma flat_obj_of_isStdCover {N : SMod O} (hN : IsStdCover N) (n : SimplexCategoryᵒᵖ) :
    Module.Flat ↥((ringPresheaf O).obj n) ↥(N.obj n) := by
  obtain hz | ⟨N', ⟨e⟩⟩ := hN
  · have : Subsingleton ↥(N.obj n) :=
      ModuleCat.isZero_iff_subsingleton.1
        (Functor.map_isZero (PresheafOfModules.evaluation (ringPresheaf O) n) hz)
    infer_instance
  · have : Module.Flat ↥((ringPresheaf O).obj n)
        ↥((PresheafOfModules.evaluation (ringPresheaf O) n).obj N'.stdCover') :=
      flat_stdCover_obj N' n
    exact Module.Flat.of_linearEquiv
      ((PresheafOfModules.evaluation (ringPresheaf O) n).mapIso e).toLinearEquiv

/-- **A simplicial module with flat sections, placed in degree zero, has flat sections in every
degree of the resulting complex**: in degree `0` they are its own, and elsewhere they are a
subsingleton. -/
lemma flat_single_obj {M : SMod O} (hM : ∀ n, Module.Flat ↥((ringPresheaf O).obj n) ↥(M.obj n))
    (p : ℤ) (n : SimplexCategoryᵒᵖ) :
    Module.Flat ↥((ringPresheaf O).obj n)
      ↥((((HomologicalComplex.single (SMod O) (ComplexShape.up ℤ) 0).obj M).X p).obj n) := by
  by_cases hp : p = 0
  · subst hp
    have : Module.Flat ↥((ringPresheaf O).obj n)
        ↥((PresheafOfModules.evaluation (ringPresheaf O) n).obj M) := hM n
    exact Module.Flat.of_linearEquiv
      ((PresheafOfModules.evaluation (ringPresheaf O) n).mapIso
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 M)).toLinearEquiv
  · have : Subsingleton
        ↥((((HomologicalComplex.single (SMod O) (ComplexShape.up ℤ) 0).obj M).X p).obj n) :=
      ModuleCat.isZero_iff_subsingleton.1
        (Functor.map_isZero (PresheafOfModules.evaluation (ringPresheaf O) n)
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M p hp))
    infer_instance

/-! ### The row filtration -/

/-- The row `q` of the base-changed double complex of a map of complexes of simplicial modules is
that map under the row functor. -/
lemma flipHom_baseChanged_f (q : ℤ) {K L : CochainComplex (SMod O) ℤ} (f : K ⟶ L) :
    (flipHom (((changeOfRings φ ⋙
      mooreCochain O').mapHomologicalComplex
        (ComplexShape.up ℤ)).map f)).f q =
      (((changeOfRings φ ⋙ mooreCochain O') ⋙
        HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) q).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f := rfl

/-- **The row filtration of the double complex of the Δ-instance of [Stacks, Tag 08RX] on the
base-changed side.** A quasi-isomorphism of complexes of simplicial modules, both bounded above
by `0` and both sectionwise flat, stays a quasi-isomorphism on the total complexes of the
base-changed double complexes. -/
theorem quasiIso_total_map_baseChangedMooreBicomplex
    {K L : CochainComplex (SMod O) ℤ} (f : K ⟶ L) [QuasiIso f]
    [K.IsStrictlyLE 0] [L.IsStrictlyLE 0]
    (hK : ∀ (p : ℤ) (n : SimplexCategoryᵒᵖ),
      Module.Flat ↥((ringPresheaf O).obj n) ↥((K.X p).obj n))
    (hL : ∀ (p : ℤ) (n : SimplexCategoryᵒᵖ),
      Module.Flat ↥((ringPresheaf O).obj n) ↥((L.X p).obj n)) :
    QuasiIso (HomologicalComplex₂.total.map
      (((changeOfRings φ ⋙
        mooreCochain O').mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) (ComplexShape.up ℤ)) := by
  have hz : ∀ (J : CochainComplex (SMod O) ℤ) [J.IsStrictlyLE 0] (p q : ℤ),
      0 < p ∨ 0 < q → IsZero (((baseChangedMooreBicomplex φ J).X p).X q) := by
    intro J _ p q hpq
    rcases hpq with hp | hq
    · exact Functor.map_isZero (HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ) q)
        (isZero_baseChangedMooreBicomplex_X φ J p
          (CochainComplex.isZero_of_isStrictlyLE J 0 p hp))
    · exact isZero_baseChangedMooreBicomplex_X_X φ J p q hq
  refine quasiIso_total_map_of_upperBound_flip _ 0 0 (fun p q hpq => hz K p q hpq)
    (fun p q hpq => hz L p q hpq) (fun q => ?_)
  rcases le_or_gt q 0 with hq | hq
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, (ComplexShape.embeddingUpIntLE (0 : ℤ)).f n = q :=
      ⟨(-q).toNat, by simp; omega⟩
    subst hn
    rw [flipHom_baseChanged_f φ _ f]
    have hrow : QuasiIso (((PresheafOfModules.evaluation (ringPresheaf O)
        (op (SimplexCategory.mk n)) ⋙
          ModuleCat.extendScalars (φ.app (op (SimplexCategory.mk n))).hom ⋙
            forget₂ (ModuleCat.{u} ↥(O'.obj (op (SimplexCategory.mk n))))
              AddCommGrpCat.{u}).mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
      quasiIso_eval_extendScalars_map φ n f (fun p => hK p _) (fun p => hL p _)
    have hE := Functor.mapHomologicalComplexIso (ComplexShape.up ℤ)
      (baseChangedMooreCochainCompEvalIso φ n)
    have : QuasiIso ((((changeOfRings φ ⋙
        mooreCochain O') ⋙
          HomologicalComplex.eval AddCommGrpCat.{u} (ComplexShape.up ℤ)
            ((ComplexShape.embeddingUpIntLE (0 : ℤ)).f n)).mapHomologicalComplex
              (ComplexShape.up ℤ)).map f ≫ hE.hom.app L) := by
      rw [hE.hom.naturality f]
      infer_instance
    exact quasiIso_of_comp_right _ (hE.hom.app L) (hφφ' := this)
  · have hiso : ∀ p : ℤ, IsIso (((flipHom (((changeOfRings φ ⋙
        mooreCochain O').mapHomologicalComplex
          (ComplexShape.up ℤ)).map f)).f q).f p) := fun p =>
      ⟨0, (isZero_baseChangedMooreBicomplex_X_X φ K p q hq).eq_of_src _ _,
        (isZero_baseChangedMooreBicomplex_X_X φ L p q hq).eq_of_src _ _⟩
    have : IsIso ((flipHom (((changeOfRings φ ⋙
        mooreCochain O').mapHomologicalComplex
          (ComplexShape.up ℤ)).map f)).f q) := HomologicalComplex.Hom.isIso_of_components _
    infer_instance

/-! ### The Δ-instance of Tag 08RX -/

/-- **The Δ-instance of [Stacks, Tag 08RX].** Let `O` be a simplicial commutative ring, `O'` a
simplicial commutative ring and `φ : O ⟶ O'` a homomorphism such that the base-change unit
`s(O) ⟶ s(O')` is a quasi-isomorphism of Moore complexes. Then for every simplicial `O`-module
`M` which is flat in every simplicial degree the base-change unit

`s(M) ⟶ s(M ⊗_O O')`

is a quasi-isomorphism. -/
theorem quasiIso_mooreCochainBaseChange_app (M : SMod O)
    (hM : ∀ n, Module.Flat ↥((ringPresheaf O).obj n) ↥(M.obj n))
    (hφ : QuasiIso ((alternatingFaceMapCochainComplex AddCommGrpCat.{u}).map (unitMap' φ))) :
    QuasiIso ((mooreCochainBaseChange' φ).app M) := by
  obtain ⟨L, π, hq, hP, hLE⟩ := exists_isStdCover_resolution M
  exact quasiIso_mooreCochainBaseChange_app_of_quasiIso_total_row φ M L hP π hφ
    (quasiIso_total_map_baseChangedMooreBicomplex φ π
      (fun p n => flat_obj_of_isStdCover (hP p) n) (fun p n => flat_single_obj hM p n))

end Stacks.SimplicialModules

end

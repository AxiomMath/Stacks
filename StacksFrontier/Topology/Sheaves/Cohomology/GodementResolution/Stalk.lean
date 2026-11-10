module

public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.GodementResolution.Basic
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkModulePullback
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Modules.PullbackUnderlyingSheaf

/-!
# Comparison complexes for the Godement resolution

The Godement complex of [Stacks, Tag 0FKS] is the Moore cochain complex (the alternating
coface map complex) of a cosimplicial object of endofunctors, and its augmentation comes from
the augmentation of that cosimplicial object. The clauses of 0FKS about exactness and about
stalks are proved by comparing that complex with three others, and this file provides the three
comparisons:

* the Moore cochain complex of a *constant* cosimplicial object on `A` is homotopy equivalent to
  the complex `A[0]` concentrated in degree `0` (`singleConstantHomotopyEquiv`): its
  differentials are alternately `0` and `𝟙 A`, so everything above degree `0` cancels;
* the Moore cochain complex of a cosimplicial object of functors whiskered with an additive
  functor `T` is the `T`-image of the Moore cochain complex (`alternatingWhiskerRightIso`);
* the complex of functors concentrated in degree `0` on `T`, read as a functor to complexes, is
  `T` followed by `(-)[0]` (`singleAsFunctorIso`).

## Main definitions

* `constantComplex`: the Moore cochain complex of a constant cosimplicial object.
* `singleConstantHomotopyEquiv`: the homotopy equivalence `A[0] ≃ constantComplex A`.
* `alternatingWhiskerRightIso`, `singleAsFunctorIso`: the two comparisons of functors to
  complexes.
* `restrictedStalkFunctor`: the stalk functor at `x` on `Mod(𝒪_X)` with its scalars restricted
  along the germ map `𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}` of a morphism of ringed spaces.
* `modulePullbackUnitStalkMap`: the map `M_{f(x)} ⟶ (f^* M)_x` induced by the unit of
  `f^* ⊣ f_*`, with its germ square `germ_comp_modulePullbackUnitStalkMap`.

## References

* [Stacks Project, Tag 0FKS](https://stacks.math.columbia.edu/tag/0FKS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite
open SSet Simplicial AlgebraicTopology
open scoped ZeroObject

universe u v w

namespace AlgebraicGeometry.GodementResolution

/-! ### The Moore cochain complex of a constant cosimplicial object

The alternating coface map complex of the constant cosimplicial object on `A` has every term
`A` and differential `∑_{i} (-1)^i 𝟙 A` out of degree `n`, a sum of `n + 2` terms: so the
differential is `0` out of even degrees and `𝟙 A` out of odd degrees, and the complex is
`A →0→ A →1→ A →0→ A →1→ ⋯`. It is therefore homotopy equivalent to `A[0]`. -/

section ConstantComplex

variable {C : Type v} [Category.{w} C] [Preadditive C]

/-- The Moore cochain complex of the constant cosimplicial object on `A`: every term is `A`,
and the differentials alternate between `0` and `𝟙 A`.

It is spelled as the `CochainComplex.of` it unfolds to, rather than as
`AlternatingCofaceMapComplex.obj ((Functor.const SimplexCategory).obj A)`, so that its terms are
*reducibly* `A` — `constantComplex_eq` records that the two are the same complex. The homotopy
below is a family of copies of `𝟙 A`, and writing it down needs the terms to be `A` without
unfolding a semireducible definition. -/
noncomputable abbrev constantComplex (A : C) : CochainComplex C ℕ :=
  CochainComplex.of (fun _ : ℕ => A)
    (AlternatingCofaceMapComplex.objD ((Functor.const SimplexCategory).obj A))
    (AlternatingCofaceMapComplex.d_squared ((Functor.const SimplexCategory).obj A))

/-- `constantComplex A` is the Moore cochain complex of the constant cosimplicial object. -/
lemma constantComplex_eq (A : C) :
    constantComplex A =
      AlternatingCofaceMapComplex.obj ((Functor.const SimplexCategory).obj A) := rfl

/-- The differential of `constantComplex A` out of degree `n` is the alternating sum of `n + 2`
copies of `𝟙 A`: zero for `n` even and `𝟙 A` for `n` odd. -/
lemma constantComplex_d (A : C) (n : ℕ) :
    (constantComplex A).d n (n + 1) = if Even n then 0 else 𝟙 A := by
  classical
  rw [show (constantComplex A).d n (n + 1) =
      AlternatingCofaceMapComplex.objD ((Functor.const SimplexCategory).obj A) n from
    CochainComplex.of_d (fun _ : ℕ => A)
      (AlternatingCofaceMapComplex.objD ((Functor.const SimplexCategory).obj A)) n]
  have hδ : ∀ i : Fin (n + 2),
      CosimplicialObject.δ ((Functor.const SimplexCategory).obj A) i = 𝟙 A := fun _ => rfl
  rw [AlternatingCofaceMapComplex.objD,
    Finset.sum_congr rfl fun (i : Fin (n + 2)) (_ : i ∈ Finset.univ) =>
      congrArg (fun z : A ⟶ A => ((-1 : ℤ) ^ (i : ℕ)) • z) (hδ i),
    ← Finset.sum_smul, Fin.sum_neg_one_pow]
  have h2 : Even (n + 2) ↔ Even n := by
    rw [show n + 2 = n + 1 + 1 from rfl, Nat.even_add_one, Nat.even_add_one, not_not]
  by_cases hn : Even n
  · rw [ite_eq_left (h2.2 hn), ite_eq_left hn, zero_smul]
  · rw [ite_eq_right (fun h => hn (h2.1 h)), ite_eq_right hn, one_smul]

variable [HasZeroObject C]

/-- The inclusion of `A[0]` into `constantComplex A` as the identity in degree `0`. -/
noncomputable def singleToConstant (A : C) :
    (CochainComplex.single₀ C).obj A ⟶ constantComplex A :=
  (CochainComplex.fromSingle₀Equiv _ A).symm
    ⟨𝟙 A, by
      rw [constantComplex_d A 0, ite_eq_left (show Even 0 by decide)]
      exact comp_zero⟩

/-- The projection of `constantComplex A` onto `A[0]`, the identity in degree `0`. -/
noncomputable def constantToSingle (A : C) :
    constantComplex A ⟶ (CochainComplex.single₀ C).obj A :=
  (CochainComplex.toSingle₀Equiv _ A).symm (𝟙 A)

/-- The contracting homotopy of `constantComplex A`: in degrees above `0` the complex is
`A →1→ A →0→ A →1→ ⋯`, and `𝟙 A` in every slot `i = j + 1` is a homotopy from the identity to
the composite through `A[0]`. -/
noncomputable def constantHomotopy (A : C) :
    Homotopy (𝟙 (constantComplex A)) (constantToSingle A ≫ singleToConstant A) where
  hom i j := if i = j + 1 then 𝟙 A else 0
  zero i j h := by
    split_ifs with h'
    · exact absurd h'.symm h
    · rfl
  comm n := by
    classical
    have hz : (singleToConstant A).f 0 = 𝟙 A :=
      CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
    have hz' : (constantToSingle A).f 0 = 𝟙 A :=
      CochainComplex.toSingle₀Equiv_symm_apply_f_zero _
    rw [dNext_eq _ (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]
    cases n with
    | zero =>
      rw [prevD_eq_zero _ 0 (by simp), HomologicalComplex.id_f,
        HomologicalComplex.comp_f, hz, hz', constantComplex_d A 0,
        ite_eq_left (show Even 0 by decide), ite_eq_left rfl]
      simp
    | succ n =>
      rw [prevD_eq _ (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl),
        HomologicalComplex.id_f, HomologicalComplex.comp_f]
      have hp : (constantToSingle A).f (n + 1) = 0 :=
        CochainComplex.toSingle₀Equiv_symm_apply_f_succ _ _
      rw [hp, zero_comp, add_zero, ite_eq_left rfl, ite_eq_left rfl,
        constantComplex_d A n, constantComplex_d A (n + 1)]
      by_cases hn : Even n
      · rw [ite_eq_left hn, ite_eq_right (fun h => Nat.even_add_one.mp h hn)]
        simp
      · rw [ite_eq_right hn, ite_eq_left (Nat.even_add_one.mpr hn)]
        simp

/-- **The Moore cochain complex of a constant cosimplicial object is homotopy equivalent to the
complex concentrated in degree `0`.** The equivalence is the identity of `A` in degree `0` both
ways, with `constantHomotopy` contracting the rest. -/
noncomputable def singleConstantHomotopyEquiv (A : C) :
    HomotopyEquiv ((CochainComplex.single₀ C).obj A) (constantComplex A) where
  hom := singleToConstant A
  inv := constantToSingle A
  homotopyHomInvId := Homotopy.ofEq (by
    apply HomologicalComplex.from_single_hom_ext
    have hz : (singleToConstant A).f 0 = 𝟙 A :=
      CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _
    have hz' : (constantToSingle A).f 0 = 𝟙 A :=
      CochainComplex.toSingle₀Equiv_symm_apply_f_zero _
    rw [HomologicalComplex.comp_f, HomologicalComplex.id_f, hz, hz']
    exact Category.id_comp _)
  homotopyInvHomId := (constantHomotopy A).symm

/-- `singleConstantHomotopyEquiv` is the identity in degree `0`. -/
lemma singleConstantHomotopyEquiv_hom_f_zero (A : C) :
    (singleConstantHomotopyEquiv A).hom.f 0 = 𝟙 A :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

end ConstantComplex

/-! ### Whiskering a cosimplicial object of functors with an additive functor -/

section Whiskering

variable {C : Type u} [Category.{v} C] {D : Type*} [Category D]
  {E : Type*} [Category E] [Preadditive D] [Preadditive E]

/-- The Moore cochain complex of a cosimplicial object of functors `C ⥤ D` whiskered with an
additive functor `T : D ⥤ E`, read as a functor `C ⥤ CochainComplex E ℕ`, is the Moore cochain
complex of the original followed by `T` applied degreewise. Both sides are the identity in
every degree; the content is that `T` commutes with the alternating sums of cofaces. -/
noncomputable def alternatingWhiskerRightIso
    (Q : CosimplicialObject (C ⥤ D)) (T : D ⥤ E) [T.Additive] :
    (AlternatingCofaceMapComplex.obj
      (Q ⋙ (Functor.whiskeringRight C D E).obj T)).asFunctor ≅
      (AlternatingCofaceMapComplex.obj Q).asFunctor ⋙
        T.mapHomologicalComplex (ComplexShape.up ℕ) := by
  refine NatIso.ofComponents (fun A => HomologicalComplex.Hom.isoOfComponents
    (fun n => Iso.refl _) (fun i j hij => ?_)) ?_
  · obtain rfl : i + 1 = j := hij
    change (𝟙 _) ≫ T.map (((AlternatingCofaceMapComplex.obj Q).d i (i + 1)).app A) =
      ((AlternatingCofaceMapComplex.obj
        (Q ⋙ (Functor.whiskeringRight C D E).obj T)).d i (i + 1)).app A ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    have hd (Q : CosimplicialObject (C ⥤ D)) :
        (AlternatingCofaceMapComplex.obj Q).d i (i + 1) =
          AlternatingCofaceMapComplex.objD Q i :=
      CochainComplex.of_d (fun n => Q.obj (.mk n)) _ i
    have he (Q : CosimplicialObject (C ⥤ E)) :
        (AlternatingCofaceMapComplex.obj Q).d i (i + 1) =
          AlternatingCofaceMapComplex.objD Q i :=
      CochainComplex.of_d (fun n => Q.obj (.mk n)) _ i
    rw [hd, he]
    simp only [AlternatingCofaceMapComplex.objD, CosimplicialObject.δ,
      NatTrans.app_sum, NatTrans.app_zsmul,
      Functor.comp_map, Functor.whiskeringRight_obj_map, Functor.whiskerRight_app]
    exact (T.map_sum
        (fun k : Fin (i + 2) => ((-1 : ℤ) ^ (k : ℕ)) • (Q.map (SimplexCategory.δ k)).app A)
        Finset.univ).trans
      (Finset.sum_congr rfl fun _ _ => T.map_zsmul)
  · intro A B f
    ext n
    change T.map ((Q.obj (.mk n)).map f) ≫ 𝟙 _ = 𝟙 _ ≫ T.map ((Q.obj (.mk n)).map f)
    simp

/-- `alternatingWhiskerRightIso` is the identity in every degree. -/
lemma alternatingWhiskerRightIso_hom_f
    (Q : CosimplicialObject (C ⥤ D)) (T : D ⥤ E) [T.Additive] (A : C) (n : ℕ) :
    ((alternatingWhiskerRightIso Q T).hom.app A).f n =
      𝟙 (T.obj ((Q.obj (.mk n)).obj A)) := rfl

/-- The complex of functors `C ⥤ D` concentrated in degree `0` on `T`, read as a functor
`C ⥤ CochainComplex D ℕ`, is `T` followed by the degree-`0` complex functor. -/
noncomputable def singleAsFunctorIso [HasZeroObject D] (T : C ⥤ D) :
    ((HomologicalComplex.single (C ⥤ D) (ComplexShape.up ℕ) 0).obj T).asFunctor ≅
      T ⋙ CochainComplex.single₀ D := by
  refine NatIso.ofComponents (fun A => HomologicalComplex.Hom.isoOfComponents
    (fun n => ?_) (fun i j hij => ?_)) ?_
  · cases n with
    | zero => exact Iso.refl (T.obj A)
    | succ n =>
      exact (Functor.map_isZero ((evaluation C D).obj A)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 T (n + 1)
          (by omega))).iso
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 (T.obj A) (n + 1)
          (by omega))
  · have h1 : (((HomologicalComplex.single (C ⥤ D) (ComplexShape.up ℕ) 0).obj
        T).asFunctor.obj A).d i j = 0 := rfl
    have h2 : ((T ⋙ CochainComplex.single₀ D).obj A).d i j = 0 := rfl
    rw [h1, h2, zero_comp, comp_zero]
  · intro A B f
    ext n
    cases n with
    | zero =>
      refine (Category.comp_id (T.map f)).trans ?_
      simp only [Functor.comp_obj, evaluation_obj_obj, Functor.comp_map, HomologicalComplex.comp_f,
        CochainComplex.single₀_obj_zero, HomologicalComplex.Hom.isoOfComponents_hom_f,
        CochainComplex.single₀_map_f_zero]
      all_goals exact (Category.id_comp (T.map f)).symm
    | succ n =>
      exact (Functor.map_isZero ((evaluation C D).obj A)
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 T (n + 1)
          (by omega))).eq_of_src _ _

/-- `singleAsFunctorIso` is the identity in degree `0`. -/
lemma singleAsFunctorIso_hom_f_zero [HasZeroObject D] (T : C ⥤ D) (A : C) :
    ((singleAsFunctorIso T).hom.app A).f 0 = 𝟙 (T.obj A) := rfl

end Whiskering

/-! ### Two identities used to feed the standard resolution to [Stacks, Tag 08ND] -/

/-- A transformation into a composite with `H` is unchanged by composing with identities and
with `𝟙` whiskered into `H`: the shape in which [Stacks, Tag 08ND] states its degeneracy
hypothesis. -/
lemma eq_id_comp_comp_whiskerRight_id {C : Type u} [Category.{v} C]
    {K F : C ⥤ C} (H : C ⥤ C) (f : F ⟶ K ⋙ H) :
    f = 𝟙 F ≫ f ≫ Functor.whiskerRight (𝟙 K) H ≫ 𝟙 (K ⋙ H) := by
  rw [Functor.whiskerRight_id']
  simp

/-- The term of `resolutionComplex Q` in degree `n` is the `n`-th term of the cosimplicial
object `Q`, by the identity in each component. -/
noncomputable def resolutionTermIso {C : Type v} [Category.{w, v} C]
    [Abelian C] (Q : CosimplicialObject.Augmented (C ⥤ C)) (n : ℕ) :
    resolutionComplex Q ⋙ HomologicalComplex.eval C (ComplexShape.up ℕ) n ≅
      Q.right.obj (.mk n) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro A B f
    dsimp [resolutionComplex, HomologicalComplex.complexOfFunctorsToFunctorToComplex,
      HomologicalComplex.asFunctor]
    change (Q.right.obj (.mk n)).map f ≫ 𝟙 _ = 𝟙 _ ≫ (Q.right.obj (.mk n)).map f
    simp)

/-- The augmentation `resolutionAugmentation Q hL` is, in degree `0`, the augmentation of the
cosimplicial object `Q`. -/
lemma resolutionAugmentation_app_f_zero {C : Type v} [Category.{w} C]
    [Abelian C] (Q : CosimplicialObject.Augmented (C ⥤ C))
    (hL : Q.left = 𝟭 C) (A : C) :
    ((resolutionAugmentation Q hL).app A).f 0 =
      (eqToHom hL.symm ≫ Q.hom.app (.mk 0)).app A :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-! ### The stalk of a pullback of sheaves of modules

For a morphism of ringed spaces `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and a point `x` of `X`, the unit of
`f^* ⊣ f_*` induces a map `M_{f(x)} ⟶ (f^* M)_x` on the stalks of the underlying presheaves of
abelian groups: take the stalk at `f x` of `M ⟶ f_* f^* M`, then the canonical map out of the
stalk of a pushforward. It is semilinear over the germ map `𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}`, so it is a
morphism of `𝒪_{Y,f(x)}`-modules once the scalars of `(f^* M)_x` are restricted along that germ
map, which is what `restrictedStalkFunctor` does.

By [Stacks, Tag 0098] the stalk `(f^* M)_x` is `𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} M_{f(x)}` and this map is
`m ↦ 1 ⊗ m`, so it is bijective as soon as the germ map is. That is the case for the morphism
`f : X_disc ⟶ X` of the Godement construction, `f` being the identity on points. -/

section PullbackStalk

open RingedSpaceModuleAdjunction

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (x : X)

/-- The stalk functor at `x` on `Mod(𝒪_X)` with its scalars restricted along the germ map
`𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}` of `f`, so that it has the same target as the stalk functor at `f x` on
`Mod(𝒪_Y)`. -/
noncomputable def restrictedStalkFunctor :
    SheafOfModules.{u} (structureSheafRing X) ⥤
      ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
        (structureSheafRing Y).obj (f.hom.base x)) :=
  AlgebraicGeometry.SheafOfModules.stalkFunctor (structureSheafRing X) x ⋙
    ModuleCat.restrictScalars.{u, u, u} (Stacks.RingedSpace.stalkRingMap f x).hom

/-- The presheaf of abelian groups underlying a sheaf of modules on a ringed space, in the
spelling `PresheafOfModules.toPresheaf` produces: the same presheaf as `M.val.presheaf`, but
reducibly the object a stalk functor is applied to, which is what the germ lemmas below need in
order to rewrite. -/
noncomputable abbrev modulePresheaf {Z : RingedSpace.{u, u}}
    (M : SheafOfModules.{u} (structureSheafRing Z)) :
    TopCat.Presheaf AddCommGrpCat.{u} Z.carrier :=
  (PresheafOfModules.toPresheaf (structureSheafRing Z).obj).obj M.val

/-- The map `M_{f(x)} ⟶ (f^* M)_x` on stalks of underlying presheaves of abelian groups induced
by the unit `M ⟶ f_* f^* M` of `f^* ⊣ f_*`, followed by the canonical map out of the stalk of a
pushforward. -/
noncomputable def modulePullbackUnitStalkMap (M : SheafOfModules.{u} (structureSheafRing Y)) :
    TopCat.Presheaf.stalk (C := AddCommGrpCat.{u}) (modulePresheaf M) (f.hom.base x) ⟶
      TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (modulePresheaf ((modulePullback f).obj M)) x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f.hom.base x)).map
      ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map
        ((modulePullbackPushforwardAdjunction f).unit.app M).val) ≫
    TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
      (modulePresheaf ((modulePullback f).obj M)) x

/-- **The germ square of the pullback unit.** The germ at `x` over `f⁻¹V` of the image of a
section of `M` over `V` under the unit is the image under `modulePullbackUnitStalkMap` of its
germ at `f x`.

The proof is in term mode on purpose: `rw` builds a motive that is rejected because
`(modulePresheaf M).stalk x` and `(stalkFunctor AddCommGrpCat x).obj (modulePresheaf M)` are
equal only up to unfolding a semireducible definition, which the two germ lemmas being combined
here already do in their own statements. -/
theorem germ_comp_modulePullbackUnitStalkMap (M : SheafOfModules.{u} (structureSheafRing Y))
    (V : Opens Y.carrier) (hV : f.hom.base x ∈ V) :
    TopCat.Presheaf.germ (C := AddCommGrpCat.{u}) (modulePresheaf M) V (f.hom.base x) hV ≫
        modulePullbackUnitStalkMap f x M =
      ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map
          ((modulePullbackPushforwardAdjunction f).unit.app M).val).app (op V) ≫
        TopCat.Presheaf.germ (C := AddCommGrpCat.{u})
          (modulePresheaf ((modulePullback f).obj M))
          ((Opens.map f.hom.base).obj V) x hV :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ TopCat.Presheaf.stalkPushforward AddCommGrpCat.{u} f.hom.base
          (modulePresheaf ((modulePullback f).obj M)) x)
        (TopCat.Presheaf.stalkFunctor_map_germ V (f.hom.base x) hV
          ((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map
            ((modulePullbackPushforwardAdjunction f).unit.app M).val))).trans
      ((Category.assoc _ _ _).trans
        (congrArg
          (((PresheafOfModules.toPresheaf (structureSheafRing Y).obj).map
            ((modulePullbackPushforwardAdjunction f).unit.app M).val).app (op V) ≫ ·)
          (TopCat.Presheaf.stalkPushforward_germ AddCommGrpCat.{u} f.hom.base
            (modulePresheaf ((modulePullback f).obj M)) V x hV))))

end PullbackStalk

end AlgebraicGeometry.GodementResolution

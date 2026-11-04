module

public import StacksFrontier.Topology.Sheaves.Cohomology.GodementResolution.Stalk
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ClosedSubsetPullbackLeftExact
public import StacksFrontier.Topology.Sheaves.Modules.StalkAcyclic
import StacksCore.Tactic.StacksAttribute

/-!
# The Godement resolution is a stalkwise homotopy equivalence

This file proves clauses (3) and (5) of [Stacks, Tag 0FKS] for the Godement complex of
`StacksFrontier/Topology/Sheaves/Cohomology/GodementResolution/Basic.lean`: the augmentation
`F[0] ⟶ G(F)` of the Godement complex becomes a homotopy equivalence on every stalk, naturally
in `F`, and is therefore a quasi-isomorphism.

## References

* [Stacks Project, Tag 0FKS](https://stacks.math.columbia.edu/tag/0FKS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite
open SSet Simplicial AlgebraicTopology

universe u

namespace AlgebraicGeometry.GodementResolution

open RingedSpaceModuleAdjunction Stacks.RingedSpace

/-! ### The stalk of a pullback along a morphism with invertible germ maps -/

section PullbackStalkIso

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) (x : X)

/-- When the germ map `𝒪_{Y,f(x)} ⟶ 𝒪_{X,x}` of `f` is invertible, base change along it followed
by restriction of scalars along it is the identity functor on `𝒪_{Y,f(x)}`-modules.

`stalkBaseChange f x` is `ModuleCat.extendScalars` of the germ map, left adjoint to
`ModuleCat.restrictScalars`; when the germ map is invertible the latter is an equivalence, so the
former is its inverse by uniqueness of left adjoints. -/
noncomputable def stalkBaseChangeRestrictIso (h : IsIso (stalkRingMap f x)) :
    stalkBaseChange f x ⋙ ModuleCat.restrictScalars.{u, u, u} (stalkRingMap f x).hom ≅
      𝟭 (ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := Y.carrier)
        (structureSheafRing Y).obj (f.hom.base x))) := by
  let _ := structureStalkCommRing Y (f.hom.base x)
  let _ := structureStalkCommRing X x
  let e : _ ≃+* _ := (@asIso _ _ _ _ _ h).ringCatIsoToRingEquiv
  have hres : (ModuleCat.restrictScalars.{u, u, u} (stalkRingMap f x).hom).IsEquivalence :=
    ModuleCat.restrictScalars_isEquivalence_of_ringEquiv e
  let F := ModuleCat.restrictScalars.{u, u, u} (stalkRingMap f x).hom
  exact Functor.isoWhiskerRight
      ((ModuleCat.extendRestrictScalarsAdj.{u, u, u} (stalkRingMap f x).hom).leftAdjointUniq
        F.asEquivalence.symm.toAdjunction) F ≪≫
    F.asEquivalence.counitIso

/-- **The stalk functor factors through the pullback when the germ maps are invertible.** For a
morphism of ringed spaces `f` whose germ map at `x` is invertible, the stalk functor at `f x` on
`Mod(𝒪_Y)` is `f^*` followed by the stalk functor at `x` with scalars restricted along that germ
map.

This is Stacks 0098 (`Stacks.RingedSpace.stalkModulePullbackFunctorIso`) together with
`stalkBaseChangeRestrictIso`: the stalk of `f^* M` at `x` is `𝒪_{X,x} ⊗_{𝒪_{Y,f(x)}} M_{f(x)}`,
which is `M_{f(x)}` again once the germ map is invertible. -/
noncomputable def restrictedStalkPullbackIso (h : IsIso (stalkRingMap f x)) :
    SheafOfModules.stalkFunctor (structureSheafRing Y) (f.hom.base x) ≅
      modulePullback f ⋙ restrictedStalkFunctor f x :=
  (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft (SheafOfModules.stalkFunctor (structureSheafRing Y) (f.hom.base x))
      (stalkBaseChangeRestrictIso f x h).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (stalkModulePullbackFunctorIso f x).symm
      (ModuleCat.restrictScalars.{u, u, u} (stalkRingMap f x).hom) ≪≫
    Functor.associator _ _ _

end PullbackStalkIso

/-! ### The germ maps of `f : X_disc ⟶ X` -/

/-- The germ map of `f : X_disc ⟶ X` on structure sheaves is invertible, in the `RingCat`-valued
spelling that `SheafOfModules` uses: `fromDiscrete_stalkMap_bijective` says the `CommRingCat`
one is bijective, and `Stacks.RingedSpace.isIso_stalkRingMap_of_isIso_stalkMap` transports
that. -/
theorem isIso_stalkRingMap_fromDiscrete (X : RingedSpace.{u, u})
    (x : discreteRingedSpace X) :
    IsIso (stalkRingMap (fromDiscrete X) x) :=
  isIso_stalkRingMap_of_isIso_stalkMap (fromDiscrete X) x
    ((ConcreteCategory.isIso_iff_bijective _).2 (fromDiscrete_stalkMap_bijective X x))

/-- **The stalk functor on `Mod(𝒪_X)` factors through `f^*` for the Godement morphism.** The
stalk at `x` is `f^*` followed by the stalk at the point of `X_disc` over `x`, with scalars
restricted along the germ map — which is invertible by `isIso_stalkRingMap_fromDiscrete`. -/
noncomputable def godementStalkPullbackIso (X : RingedSpace.{u, u}) (x : X) :
    SheafOfModules.stalkFunctor (structureSheafRing X) x ≅
      modulePullback (fromDiscrete X) ⋙
        restrictedStalkFunctor (fromDiscrete X) (discretePoint X x) :=
  restrictedStalkPullbackIso (fromDiscrete X) (discretePoint X x)
    (isIso_stalkRingMap_fromDiscrete X (discretePoint X x))

/-! ### Quasi-isomorphy of cochain complexes indexed by `ℕ` is stalkwise

`AlgebraicGeometry.SheafOfModules.quasiIso_of_forall_stalk_quasiIso` is stated for cochain
complexes indexed by `ℤ`, and the Godement complex is indexed by `ℕ`; the proof is the same and
uses nothing about the indexing. -/

section StalkwiseQuasiIso

variable {Z : TopCat.{u}} (𝒪 : CategoryTheory.Sheaf (Opens.grothendieckTopology Z) RingCat.{u})

/-- The map induced on homology in degree `n` by a morphism of cochain complexes of sheaves of
`𝒪`-modules indexed by `ℕ` is an isomorphism exactly when every one of its stalks is: the stalk
functor preserves homology, and isomorphy of sheaves of modules is stalkwise. -/
theorem isIso_homologyMap_iff_forall_stalk_nat
    {K L : CochainComplex (SheafOfModules.{u} 𝒪) ℕ} (φ : K ⟶ L) (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap φ n) ↔ ∀ z : Z,
      IsIso (HomologicalComplex.homologyMap
        (((SheafOfModules.stalkFunctor 𝒪 z).mapHomologicalComplex
          (ComplexShape.up ℕ)).map φ) n) := by
  rw [SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map]
  exact forall_congr' fun z => (NatIso.isIso_map_iff
    (ShortComplex.homologyFunctorIso (SheafOfModules.stalkFunctor 𝒪 z))
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) n).map φ)).symm

/-- **Stalkwise criterion for quasi-isomorphy of `ℕ`-indexed cochain complexes.** -/
theorem quasiIso_of_forall_stalk_quasiIso_nat
    {K L : CochainComplex (SheafOfModules.{u} 𝒪) ℕ} (φ : K ⟶ L)
    (h : ∀ z : Z, QuasiIso (((SheafOfModules.stalkFunctor 𝒪 z).mapHomologicalComplex
      (ComplexShape.up ℕ)).map φ)) :
    QuasiIso φ := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, isIso_homologyMap_iff_forall_stalk_nat]
  intro z
  have := h z
  exact (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance

end StalkwiseQuasiIso


/-! ### The specification of the Godement standard resolution

`godementSimplicial X` is named by `Exists.choose` in
`StacksFrontier/Topology/Sheaves/Cohomology/GodementResolution/Basic.lean`, which exposes the two
pieces of its specification that the construction of the complex needs. The splitting after `f^*`
needs the remaining three — the faces, the degeneracies and the augmentation — so they are read
off here. -/

section Specification

variable (X : RingedSpace.{u, u})

/-- The faces of `godementSimplicial X` are `Godement.face` of the counit. -/
theorem godementSimplicial_δ (n : ℕ) (j : Fin (n + 2)) :
    (godementSimplicial X).left.δ j =
      eqToHom (godementSimplicial_left_obj X (n + 1)) ≫
        Godement.face (godementComonad X).ε (n + 1) j ≫
          eqToHom (godementSimplicial_left_obj X n).symm :=
  (exists_standardResolution
    (godementComonad X)).choose_spec.choose_spec.choose_spec.1 n j

/-- The degeneracies of `godementSimplicial X` are `Godement.degeneracy` of the comultiplication.
-/
theorem godementSimplicial_σ (n : ℕ) (j : Fin (n + 1)) :
    (godementSimplicial X).left.σ j =
      eqToHom (godementSimplicial_left_obj X n) ≫
        Godement.degeneracy (godementComonad X).δ n j ≫
          eqToHom (godementSimplicial_left_obj X (n + 1)).symm :=
  (exists_standardResolution
    (godementComonad X)).choose_spec.choose_spec.choose_spec.2.1 n j

/-- The augmentation of `godementSimplicial X` is the counit. -/
theorem godementSimplicial_hom_app_zero :
    (godementSimplicial X).hom.app (op ⦋0⦌) =
      eqToHom (godementSimplicial_left_obj X 0) ≫
        Godement.face (godementComonad X).ε 0 0 ≫
          eqToHom (godementSimplicial_right X).symm :=
  (exists_standardResolution
    (godementComonad X)).choose_spec.choose_spec.choose_spec.2.2

end Specification

/-! ### The splitting of the Godement standard resolution after `f^*`

[Stacks, Tag 08ND]
(`CategoryTheory.Adjunction.exists_homotopyInverse_whiskered_standardResolution`) says that the
standard resolution of an adjunction becomes simplicially contractible after whiskering with either
functor of the adjunction. For the Godement comonad the right whiskering is with `(f^*)ᵒᵖ`, and
that is what makes the Godement complex stalkwise split: on stalks `f^*` is the identity, by
`godementStalkPullbackIso`. -/

section Splitting

variable (X : RingedSpace.{u, u})

/-- Whiskering endofunctors of `Mod(𝒪_X)ᵒᵖ` on the right with `(f^*)ᵒᵖ`. -/
noncomputable abbrev opPullbackWhiskerRight :
    ((SheafOfModules.{u} (structureSheafRing X))ᵒᵖ ⥤
        (SheafOfModules.{u} (structureSheafRing X))ᵒᵖ) ⥤
      ((SheafOfModules.{u} (structureSheafRing X))ᵒᵖ ⥤
        (SheafOfModules.{u} (structureSheafRing (discreteRingedSpace X)))ᵒᵖ) :=
  (Functor.whiskeringRight _ _ _).obj (modulePullback (fromDiscrete X)).op

/-- Precomposing endofunctors of `Mod(𝒪_X)ᵒᵖ` with `(f_*)ᵒᵖ`. -/
noncomputable abbrev opPushforwardWhiskerLeft :
    ((SheafOfModules.{u} (structureSheafRing X))ᵒᵖ ⥤
        (SheafOfModules.{u} (structureSheafRing X))ᵒᵖ) ⥤
      ((SheafOfModules.{u} (structureSheafRing (discreteRingedSpace X)))ᵒᵖ ⥤
        (SheafOfModules.{u} (structureSheafRing X))ᵒᵖ) :=
  (Functor.whiskeringLeft _ _ _).obj (modulePushforward (fromDiscrete X)).op

/-- The augmentation of `godementSimplicial X`, whiskered on the right with `(f^*)ᵒᵖ`. -/
noncomputable def godementAugWhiskerRight :
    (godementSimplicial X).left ⋙ opPullbackWhiskerRight X ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj
        ((godementSimplicial X).right ⋙ (modulePullback (fromDiscrete X)).op) where
  app k := Functor.whiskerRight ((godementSimplicial X).hom.app k) _
  naturality i j g := by
    change (opPullbackWhiskerRight X).map ((godementSimplicial X).left.map g) ≫
        (opPullbackWhiskerRight X).map ((godementSimplicial X).hom.app j) =
      (opPullbackWhiskerRight X).map ((godementSimplicial X).hom.app i)
    have hn : (godementSimplicial X).left.map g ≫ (godementSimplicial X).hom.app j =
        (godementSimplicial X).hom.app i := by
      simp
    rw [← Functor.map_comp]
    exact congrArg (opPullbackWhiskerRight X).map hn

/-- The augmentation of `godementSimplicial X`, whiskered on the left with `(f_*)ᵒᵖ`. -/
noncomputable def godementAugWhiskerLeft :
    (godementSimplicial X).left ⋙ opPushforwardWhiskerLeft X ⟶
      (Functor.const SimplexCategoryᵒᵖ).obj
        ((modulePushforward (fromDiscrete X)).op ⋙ (godementSimplicial X).right) where
  app k := Functor.whiskerLeft _ ((godementSimplicial X).hom.app k)
  naturality i j g := by
    change (opPushforwardWhiskerLeft X).map ((godementSimplicial X).left.map g) ≫
        (opPushforwardWhiskerLeft X).map ((godementSimplicial X).hom.app j) =
      (opPushforwardWhiskerLeft X).map ((godementSimplicial X).hom.app i)
    have hn : (godementSimplicial X).left.map g ≫ (godementSimplicial X).hom.app j =
        (godementSimplicial X).hom.app i := by
      simp
    rw [← Functor.map_comp]
    exact congrArg (opPushforwardWhiskerLeft X).map hn

/-- **The Godement standard resolution is simplicially contractible after `f^*`.**
[Stacks, Tag 08ND] applied to the adjunction `(f^*)ᵒᵖ ⊣ (f_*)ᵒᵖ` and to the standard resolution
`godementSimplicial X` of its comonad.

The comonad, its iterates, its counit and its comultiplication are introduced as local
definitions, so that the four coherence conditions of [Stacks, Tag 08ND] — which compare
`Godement.face` and `Godement.degeneracy` with the whiskerings of the counit and the
comultiplication across the identification `T^{n+1} = T^n ∘ T` — can be discharged by unfolding
exactly those definitions. Written out, the two sides of each condition differ by that
identification and `simp` has nothing to unfold. -/
theorem exists_homotopyInverse_godementAugWhiskerRight :
    ∃ r : (Functor.const SimplexCategoryᵒᵖ).obj
        ((godementSimplicial X).right ⋙ (modulePullback (fromDiscrete X)).op) ⟶
      (godementSimplicial X).left ⋙ opPullbackWhiskerRight X,
      Relation.EqvGen (fun g₁ g₂ => Nonempty (SimplicialObject.Homotopy g₁ g₂))
        (godementAugWhiskerRight X ≫ r) (𝟙 _) ∧
      Relation.EqvGen (fun g₁ g₂ => Nonempty (SimplicialObject.Homotopy g₁ g₂))
        (r ≫ godementAugWhiskerRight X) (𝟙 _) := by
  let adjOpp := (modulePullbackPushforwardAdjunction (fromDiscrete X)).op
  let com := adjOpp.toComonad
  let Z : ℕ → ((SheafOfModules.{u} (structureSheafRing X))ᵒᵖ ⥤
      (SheafOfModules.{u} (structureSheafRing X))ᵒᵖ) :=
    fun n => Functor.iterate adjOpp.toComonad.toFunctor n
  let dd : adjOpp.toComonad.toFunctor ⟶ 𝟭 _ := adjOpp.toComonad.ε
  let ss : adjOpp.toComonad.toFunctor ⟶
    adjOpp.toComonad.toFunctor ⋙ adjOpp.toComonad.toFunctor := adjOpp.toComonad.δ
  let d : (n : ℕ) → Fin (n + 1) → (Z (n + 1) ⟶ Z n) := fun n => Godement.face dd n
  let s : (n : ℕ) → Fin (n + 1) → (Z (n + 1) ⟶ Z (n + 2)) := fun n => Godement.degeneracy ss n
  exact (CategoryTheory.Adjunction.exists_homotopyInverse_whiskered_standardResolution
    adjOpp Z (fun _ => rfl) d s rfl
    (fun n => by
      show Godement.face dd n 0 = _
      rw [Godement.Prep.face_zero]
      simp [dd, Z])
    (fun n j => by
      show Godement.face dd (n + 1) j.succ = _
      rw [Godement.Prep.face_succ]
      simp [d, dd, Z])
    (fun n => by
      show Godement.degeneracy ss n 0 = _
      rw [Godement.Prep.degeneracy_zero]
      exact eq_id_comp_comp_whiskerRight_id
        (K := Functor.iterate adjOpp.toComonad.toFunctor (n + 1))
        adjOpp.toComonad.toFunctor _)
    (fun n j => by
      show Godement.degeneracy ss (n + 1) j.succ = _
      rw [Godement.Prep.degeneracy_succ]
      simp [s, ss, Z])
    (godementSimplicial X) (godementSimplicial_left_obj X) (godementSimplicial_right X)
    (godementSimplicial_δ X) (godementSimplicial_σ X) (godementSimplicial_hom_app_zero X)
    (godementAugWhiskerRight X) (fun _ => rfl)
    (godementAugWhiskerLeft X) (fun _ => rfl)).1

end Splitting


/-! ### Clause (5) of [Stacks, Tag 0FKS]: the stalkwise homotopy equivalence -/

section NaturalStalkHomotopy

variable (X : RingedSpace.{u, u})

/-- The category of modules over the stalk `𝒪_{X,x}` of the structure sheaf. -/
abbrev StalkModuleCat (x : X) : Type (u + 1) :=
  ModuleCat.{u} (TopCat.Presheaf.stalk (C := RingCat.{u}) (X := X.carrier)
    (structureSheafRing X).obj x)

/-- **A stalkwise homotopy equivalence of a functorial resolution**, with inverse and homotopies
natural in the sheaf of modules. The comparison is pinned to the augmentation `η`, not merely to
some unspecified homotopy-equivalent map: the last clause says that `η`, read on stalks, *is* the
homotopy equivalence `e` up to the two identifications `i` and `j` of complexes of functors with
functors to complexes.

Naturality in the sheaf is what makes the construction applicable degreewise to a complex of
sheaves, which is how [Stacks, Tag 0FKT] uses it. -/
def HasNaturalStalkHomotopy
    (G : SheafOfModules.{u} (structureSheafRing X) ⥤
      CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℕ)
    (η : CochainComplex.single₀ (SheafOfModules.{u} (structureSheafRing X)) ⟶ G)
    (x : X) : Prop :=
  ∃ (H : CochainComplex (SheafOfModules.{u} (structureSheafRing X) ⥤ StalkModuleCat X x) ℕ)
    (e : HomotopyEquiv
      ((HomologicalComplex.single
        (SheafOfModules.{u} (structureSheafRing X) ⥤ StalkModuleCat X x)
        (ComplexShape.up ℕ) 0).obj (SheafOfModules.stalkFunctor (structureSheafRing X) x)) H)
    (i : H.asFunctor ≅ G ⋙
      (SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex
        (ComplexShape.up ℕ))
    (j : ((HomologicalComplex.single
        (SheafOfModules.{u} (structureSheafRing X) ⥤ StalkModuleCat X x) (ComplexShape.up ℕ) 0).obj
          (SheafOfModules.stalkFunctor (structureSheafRing X) x)).asFunctor ≅
      CochainComplex.single₀ (SheafOfModules.{u} (structureSheafRing X)) ⋙
        (SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex
          (ComplexShape.up ℕ)),
    j.hom ≫ Functor.whiskerRight η
        ((SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex
          (ComplexShape.up ℕ)) =
      HomologicalComplex.complexOfFunctorsToFunctorToComplex.map e.hom ≫ i.hom

/-- The equivalence `(Mod(𝒪_X)ᵒᵖ ⥤ Mod(𝒪_{X_disc})ᵒᵖ)ᵒᵖ ≌ (Mod(𝒪_X) ⥤ Mod(𝒪_{X_disc}))`
used to turn the simplicial object of functors into a cosimplicial one. -/
noncomputable abbrev opFunctorUnop :
    ((SheafOfModules.{u} (structureSheafRing X))ᵒᵖ ⥤
        (SheafOfModules.{u} (structureSheafRing (discreteRingedSpace X)))ᵒᵖ)ᵒᵖ ⥤
      SheafOfModules.{u} (structureSheafRing X) ⥤
        SheafOfModules.{u} (structureSheafRing (discreteRingedSpace X)) :=
  (Functor.leftOpRightOpEquiv (SheafOfModules.{u} (structureSheafRing X))
      (SheafOfModules.{u} (structureSheafRing (discreteRingedSpace X)))ᵒᵖ).functor ⋙
    (Functor.whiskeringRight (SheafOfModules.{u} (structureSheafRing X))
      (SheafOfModules.{u} (structureSheafRing (discreteRingedSpace X)))ᵒᵖᵒᵖ
      (SheafOfModules.{u} (structureSheafRing (discreteRingedSpace X)))).obj (unopUnop _)

/-- **Clause (5) of [Stacks, Tag 0FKS].** On the stalk at any point `x` of `X`, the augmentation
of the Godement complex is a homotopy equivalence of complexes of `𝒪_{X,x}`-modules, naturally in
the sheaf of modules.

The proof runs the splitting of the Godement standard resolution after `f^*`
(`exists_homotopyInverse_godementAugWhiskerRight`) through the stalk functor at the point of
`X_disc` over `x`: by `godementStalkPullbackIso` the stalk functor at `x` *is* `f^*` followed by
that one, so the stalkwise Godement cosimplicial object is a cosimplicial object with a
simplicial homotopy inverse, and `homotopyEquivalences_alternatingCofaceMapComplex_map` turns a
simplicial homotopy inverse into a homotopy equivalence of Moore cochain complexes. The
comparison with the constant cosimplicial object on the stalk functor, and hence with the complex
concentrated in degree `0`, is `singleConstantHomotopyEquiv`. -/
@[sga "4 XVII 4.2.9" "special case"]
theorem hasNaturalStalkHomotopy_godementAugmentation (x : X) :
    HasNaturalStalkHomotopy X (godementComplex X) (godementAugmentation X) x := by
  let f := fromDiscrete X
  let S := godementSimplicial X
  let Q := godementCosimplicial X
  let hL : Q.left = 𝟭 (SheafOfModules.{u} (structureSheafRing X)) := godementCosimplicial_left X
  let V := (modulePullback f).op
  let WR := opPullbackWhiskerRight X
  let a := godementAugWhiskerRight X
  let Ssimp := S.left ⋙ WR
  let Tconst := (Functor.const SimplexCategoryᵒᵖ).obj (S.right ⋙ V)
  obtain ⟨r, hr₁, hr₂⟩ := exists_homotopyInverse_godementAugWhiskerRight X
  let eV := opFunctorUnop X
  let xdisc := discretePoint X x
  let K := restrictedStalkFunctor f xdisc
  let T := SheafOfModules.stalkFunctor (structureSheafRing X) x
  let β : T ≅ modulePullback f ⋙ K := godementStalkPullbackIso X x
  let Wst := (Functor.whiskeringRight (SheafOfModules.{u} (structureSheafRing X))
    (SheafOfModules.{u} (structureSheafRing (discreteRingedSpace X))) (StalkModuleCat X x)).obj K
  let Fst := eV ⋙ Wst
  let TcosSt := Tconst.rightOp ⋙ Fst
  let ScosSt := Ssimp.rightOp ⋙ Fst
  let acosSt := Functor.whiskerRight (NatTrans.rightOp a) Fst
  let rcosSt := Functor.whiskerRight (NatTrans.rightOp r) Fst
  have hcosSt₁ := by
    simpa [acosSt, rcosSt] using (CategoryTheory.homotopic_whiskerRight.2.2.1 Fst hr₂)
  have hcosSt₂ := by
    simpa [acosSt, rcosSt] using (CategoryTheory.homotopic_whiskerRight.2.2.1 Fst hr₁)
  have hTcosSt_map {n m : SimplexCategory} (u : n ⟶ m) : TcosSt.map u = 𝟙 _ := by
    simp [TcosSt, Tconst, Fst]
  have hheCosSt := AlgebraicTopology.homotopyEquivalences_alternatingCofaceMapComplex_map
    (A := SheafOfModules.{u} (structureSheafRing X) ⥤ StalkModuleCat X x)
    (U := TcosSt) (V := ScosSt) (a := acosSt)
    ⟨rcosSt,
      (by simpa [TcosSt, Tconst, V, acosSt, rcosSt, hTcosSt_map] using hcosSt₁),
      (by simpa [ScosSt, Ssimp, WR, V] using hcosSt₂)⟩
  obtain ⟨es, hes⟩ := hheCosSt
  let K₀ := (eV.obj (op (S.right ⋙ V))) ⋙ K
  let β₀ : T ≅ K₀ :=
    (Functor.leftUnitor T).symm ≪≫
      Functor.isoWhiskerRight (eqToIso hL).symm T ≪≫
      Functor.isoWhiskerLeft Q.left β
  let it : TcosSt ≅ (Functor.const SimplexCategory).obj K₀ :=
    NatIso.ofComponents (fun _ => Iso.refl _) (fun u =>
      (Category.comp_id (TcosSt.map u)).trans ((hTcosSt_map u).trans
        (Category.id_comp (((Functor.const SimplexCategory).obj K₀).map u)).symm))
  let Qst := Q.right ⋙ (Functor.whiskeringRight (SheafOfModules.{u} (structureSheafRing X))
    (SheafOfModules.{u} (structureSheafRing X)) (StalkModuleCat X x)).obj T
  let iq : ScosSt ≅ Qst :=
    NatIso.ofComponents (fun n => Functor.isoWhiskerLeft (Q.right.obj n) β.symm)
      fun u => NatTrans.ext (funext fun F => β.inv.naturality ((Q.right.map u).app F))
  let H := AlgebraicTopology.AlternatingCofaceMapComplex.obj ScosSt
  let ee := ((HomotopyEquiv.ofIso
    ((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X) ⥤ StalkModuleCat X x)
        (ComplexShape.up ℕ) 0).mapIso β₀)).trans
      (singleConstantHomotopyEquiv K₀)).trans
    ((HomotopyEquiv.ofIso
      ((AlgebraicTopology.alternatingCofaceMapComplex
        (SheafOfModules.{u} (structureSheafRing X) ⥤ StalkModuleCat X x)).mapIso it).symm).trans es)
  let ii : H.asFunctor ≅ godementComplex X ⋙ T.mapHomologicalComplex (ComplexShape.up ℕ) :=
    HomologicalComplex.complexOfFunctorsToFunctorToComplex.mapIso
      ((AlgebraicTopology.alternatingCofaceMapComplex
        (SheafOfModules.{u} (structureSheafRing X) ⥤ StalkModuleCat X x)).mapIso iq) ≪≫
      alternatingWhiskerRightIso Q.right T
  let jj := singleAsFunctorIso T ≪≫
    (HomologicalComplex.singleMapHomologicalComplex T (ComplexShape.up ℕ) 0).symm
  refine ⟨H, ee, ii, jj, ?_⟩
  apply NatTrans.ext
  funext F
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    have hj : (jj.hom.app F).f 0 = 𝟙 (T.obj F) :=
      (congrArg (· ≫ (((HomologicalComplex.singleMapHomologicalComplex T
            (ComplexShape.up ℕ) 0).symm).hom.app F).f 0)
          (singleAsFunctorIso_hom_f_zero T F)).trans (Category.id_comp _)
    have hi : (ii.hom.app F).f 0 = β.inv.app ((Q.right.obj (.mk 0)).obj F) := by
      simp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X, ii, iq]
      exact Category.comp_id _
    have hes0 : es.hom.f 0 = acosSt.app (.mk 0) := congrArg (fun φ => φ.f 0) hes
    have hee : (ee.hom.f 0).app F = β₀.hom.app F ≫ (acosSt.app (.mk 0)).app F :=
      congrArg (fun φ => φ.app F)
        (congrArg₂ (fun p q => p ≫ q)
          ((congrArg (· ≫ (singleConstantHomotopyEquiv K₀).hom.f 0)
                (HomologicalComplex.single_map_f_self (c := ComplexShape.up ℕ)
                  (j := 0) β₀.hom)).trans
            ((congrArg
                  (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 T).hom ≫ β₀.hom ≫
                    (HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0 K₀).inv) ≫ ·)
                (singleConstantHomotopyEquiv_hom_f_zero K₀)).trans
              ((Category.comp_id _).trans
                ((Category.id_comp _).trans (Category.comp_id _)))))
          ((congrArg ((((AlgebraicTopology.alternatingCofaceMapComplex
                    (SheafOfModules.{u} (structureSheafRing X) ⥤ StalkModuleCat X x)).mapIso
                  it).symm.hom).f 0 ≫ ·) hes0).trans (Category.id_comp _)))
    have hη : ((godementAugmentation X).app F).f 0 =
        (eqToHom hL.symm ≫ Q.hom.app (.mk 0)).app F :=
      resolutionAugmentation_app_f_zero Q hL F
    have hnat : T.map ((Q.hom.app (.mk 0)).app F) ≫
          β.hom.app ((Q.right.obj (.mk 0)).obj F) =
        β.hom.app (Q.left.obj F) ≫
          (modulePullback f ⋙ K).map ((Q.hom.app (.mk 0)).app F) :=
      β.hom.naturality _
    have hA : T.map ((eqToHom hL.symm).app F) ≫ β.hom.app (Q.left.obj F) = β₀.hom.app F :=
      (Category.id_comp _).symm
    have hmid : β.hom.app (Q.left.obj F) ≫
          ((modulePullback f ⋙ K).map ((Q.hom.app (.mk 0)).app F) ≫
            β.inv.app ((Q.right.obj (.mk 0)).obj F)) =
        T.map ((Q.hom.app (.mk 0)).app F) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ β.inv.app ((Q.right.obj (.mk 0)).obj F)) hnat.symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (T.map ((Q.hom.app (.mk 0)).app F) ≫ ·)
                (β.hom_inv_id_app ((Q.right.obj (.mk 0)).obj F))).trans
              (Category.comp_id _))))
    show (jj.hom.app F).f 0 ≫ T.map (((godementAugmentation X).app F).f 0) =
      (ee.hom.f 0).app F ≫ (ii.hom.app F).f 0
    refine Eq.trans ?_
      ((congrArg (· ≫ β.inv.app ((Q.right.obj (.mk 0)).obj F)) hee.symm).trans
        (congrArg ((ee.hom.f 0).app F ≫ ·) hi.symm))
    refine Eq.trans ?_
      (congrArg (fun t => (t ≫ (acosSt.app (.mk 0)).app F) ≫
        β.inv.app ((Q.right.obj (.mk 0)).obj F)) hA)
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (T.map ((eqToHom hL.symm).app F) ≫ ·) hmid).symm
    refine Eq.trans ?_ (T.map_comp _ _)
    refine Eq.trans ?_ (congrArg T.map hη)
    exact (congrArg (· ≫ T.map (((godementAugmentation X).app F).f 0)) hj).trans
      (Category.id_comp _)
  | succ n =>
    exact (Functor.map_isZero
      ((evaluation (SheafOfModules.{u} (structureSheafRing X)) (StalkModuleCat X x)).obj F)
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0 T (n + 1)
        (by omega))).eq_of_src _ _


/-- **Clause (5) of [Stacks, Tag 0FKS]**, at one sheaf and one point. The augmentation
`F[0] ⟶ (f_* f^* F → f_* f^* f_* f^* F → ⋯)` of the Godement complex, read on the stalk at `x`,
is a homotopy equivalence of complexes of `𝒪_{X,x}`-modules.

This is `hasNaturalStalkHomotopy_godementAugmentation` evaluated at `F`: evaluation at `F` is an
additive functor, so it carries the homotopy equivalence of complexes of functors to one of
complexes of modules, and the compatibility clause identifies the result with the stalk of the
augmentation up to the two isomorphisms `i` and `j`. -/
@[stacks 0FKS "the stalkwise homotopy equivalence F_x[0] ≃ ((f_* f^* F)_x → ⋯)",
  sga "4 XVII 4.2.3" "(ii)",
  sga "4 XVII 4.2" "stalkwise homotopy",
  sga "4 XVII 4.2.9" "special case"]
theorem homotopyEquivalences_stalk_godementAugmentation (x : X)
    (F : SheafOfModules.{u} (structureSheafRing X)) :
    HomologicalComplex.homotopyEquivalences (StalkModuleCat X x) (ComplexShape.up ℕ)
      (((SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex
        (ComplexShape.up ℕ)).map ((godementAugmentation X).app F)) := by
  obtain ⟨H, e, i, j, he⟩ := hasNaturalStalkHomotopy_godementAugmentation X x
  let E := (evaluation (SheafOfModules.{u} (structureSheafRing X)) (StalkModuleCat X x)).obj F
  have hm := (E.mapHomotopyEquiv e).homotopyEquivalences_hom
  have heF := congrArg (fun t => t.app F) he
  change j.hom.app F ≫ ((SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex
      (ComplexShape.up ℕ)).map ((godementAugmentation X).app F) =
    (E.mapHomologicalComplex (ComplexShape.up ℕ)).map e.hom ≫ i.hom.app F at heF
  have hf : ((SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex
        (ComplexShape.up ℕ)).map ((godementAugmentation X).app F) =
      j.inv.app F ≫ ((E.mapHomologicalComplex (ComplexShape.up ℕ)).map e.hom ≫ i.hom.app F) :=
    ((Category.id_comp _).symm.trans
        (congrArg (· ≫ ((SheafOfModules.stalkFunctor (structureSheafRing X) x).mapHomologicalComplex
            (ComplexShape.up ℕ)).map ((godementAugmentation X).app F))
          (j.inv_hom_id_app F).symm)).trans
      ((Category.assoc _ _ _).trans (congrArg (j.inv.app F ≫ ·) heF))
  have hi : IsIso (i.hom.app F) := (i.app F).isIso_hom
  have hjinv : IsIso (j.inv.app F) := (j.app F).isIso_inv
  rw [hf]
  exact (HomologicalComplex.homotopyEquivalences _ _).comp_mem _ _
    (@HomologicalComplex.homotopyEquivalences.of_isIso _ _ _ _ _ _ _ _ hjinv)
    ((HomologicalComplex.homotopyEquivalences _ _).comp_mem _ _ hm
      (@HomologicalComplex.homotopyEquivalences.of_isIso _ _ _ _ _ _ _ _ hi))

/-- **Clause (3) of [Stacks, Tag 0FKS]: the augmented Godement complex is exact.** The
augmentation `F[0] ⟶ G(F)` is a quasi-isomorphism, so
`0 → F → f_* f^* F → f_* f^* f_* f^* F → ⋯` is exact and the Godement complex is a flasque
resolution of `F`.

Quasi-isomorphy is detected on stalks (`quasiIso_of_forall_stalk_quasiIso_nat`), and on each
stalk the augmentation is a homotopy equivalence by
`homotopyEquivalences_stalk_godementAugmentation`, hence a quasi-isomorphism. -/
@[stacks 0FKS "exactness of the augmented complex 0 → F → f_* f^* F → ⋯",
  sga "4 XVII 4.2.3" "(ii)", sga "4 XVII 4.2" "augmented exactness"]
theorem quasiIso_godementAugmentation (F : SheafOfModules.{u} (structureSheafRing X)) :
    QuasiIso ((godementAugmentation X).app F) := by
  refine quasiIso_of_forall_stalk_quasiIso_nat (structureSheafRing X)
    ((godementAugmentation X).app F) fun x => ?_
  obtain ⟨e, he⟩ := homotopyEquivalences_stalk_godementAugmentation X x F
  exact he ▸ e.quasiIso_hom

end NaturalStalkHomotopy

end AlgebraicGeometry.GodementResolution

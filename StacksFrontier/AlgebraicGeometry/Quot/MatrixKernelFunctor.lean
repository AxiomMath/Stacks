module

public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafMatrices
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FpqcHomGlueUnit
public import StacksFrontier.AlgebraicGeometry.Quot.DegreeZeroSectionsLocal

/-!
# The kernel functor of a matrix of functions, in coordinates

Let `c` be a scheme of the big fppf site and `N` an `r × m` matrix of functions on `c`.  The
relative kernel functor of the morphism `𝒪^r ⟶ 𝒪^m` of `N`, on the test schemes `t : T ⟶ c`, sends
`T` to the morphisms `t^*𝒪 ⟶ t^*𝒪^r` killed by `t^*N`.  Reading such a morphism through
`t^*𝒪 ≅ 𝒪_T` and `t^*𝒪^r ≅ 𝒪_T^r` and taking its coordinates identifies the value at `T` with the
row vectors `v ∈ Γ(T, 𝒪_T)^r` with `v · t^♯N = 0`, and restriction along a morphism of test
schemes `g` with pullback of the coordinates along `g`.

## Main definitions

* `AlgebraicGeometry.Space.matKerFunctor`: the kernel functor of a matrix of functions.
* `AlgebraicGeometry.Space.kerCoord`: the coordinates of a section.
* `AlgebraicGeometry.Space.unitCoord`: the endomorphism of `𝒪` read off a morphism into an inverse
  image.

## Main results

* `AlgebraicGeometry.Space.kerCoord_mem`, `AlgebraicGeometry.Space.kerCoord_injective`,
  `AlgebraicGeometry.Space.kerCoord_surjective`: the coordinates are a bijection onto the
  solutions.
* `AlgebraicGeometry.Space.kerCoord_map`: restriction is pullback of coordinates.
* `AlgebraicGeometry.Space.unitCoord_conjHom_triangle`: reading off commutes with the comparisons
  of the pullback pseudofunctor datum of modules.

## Implementation notes

The structure sheaf enters with three spellings of its ring sheaf, all definitionally equal; the
comparison lemmas of the inverse image of `𝒪` are stated at
`SheafOfModules.unit (structureRingSheaf B S hS X)`, and that literal object is used for the source
of the kernel functor.  A projection applied to one of the heavy morphisms in play (the inverse
image comparisons, the isomorphism `f^*𝒪 ≅ 𝒪`, the coercion of `unitEndValueHom`) is unfolded by
the kernel before its arguments are compared, so equal-up-to-unfolding spellings under such a
projection are fatal; the proof of `AlgebraicGeometry.Space.kerCoord_map` therefore moves every
comparison to an equation of endomorphisms (`congrArg`) before applying the evaluation map.

## References

* [Stacks Project, Tag 08JX](https://stacks.math.columbia.edu/tag/08JX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Functor

variable {C D₁ D₂ : Type*} [Category C] [Category D₁] [Category D₂]

/-- **Conjugation along a comparison, read through isomorphisms compatible with it, is the image
under the further functor.** -/
theorem conjHom_conj_of_comp_eq {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (t : P₂ ≅ P₁ ⋙ L)
    {U : C} {U' : D₂} {V : D₁} (a : U' ≅ P₂.obj U) (b : U' ≅ L.obj V) (c : V ≅ P₁.obj U)
    (h : a.hom ≫ t.hom.app U = b.hom ≫ L.map c.hom) (γ : P₁.obj U ⟶ P₁.obj U) :
    a.hom ≫ conjHom t γ ≫ a.inv = b.hom ≫ L.map (c.hom ≫ γ ≫ c.inv) ≫ b.inv := by
  have h' : t.inv.app U ≫ a.inv = L.map c.inv ≫ b.inv := by
    have hI : a ≪≫ t.app U = b ≪≫ L.mapIso c := Iso.ext h
    exact congrArg Iso.inv hI
  simp only [conjHom, Category.assoc, Functor.map_comp]
  rw [h', ← Category.assoc, h, Category.assoc]

end CategoryTheory.Functor

namespace CategoryTheory.PullbackData

variable {A : Type*} [Category* A] {D : A → Type*} [∀ a, Category* (D a)] (P : PullbackData A D)

/-- **Conjugation along a comparison of a pullback pseudofunctor datum, read through isomorphisms
compatible with it, is the inverse image along the first factor.** -/
theorem conjHom_triangle_conj {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c} (hk : f ≫ g = k)
    {U : D c} {U' : D a} {V : D b} (α : U' ≅ (P.pull k).obj U) (β : U' ≅ (P.pull f).obj V)
    (ε : V ≅ (P.pull g).obj U)
    (h : α.hom ≫ (P.triangle hk).hom.app U = β.hom ≫ (P.pull f).map ε.hom)
    (e : (P.pull g).obj U ⟶ (P.pull g).obj U) :
    α.hom ≫ Functor.conjHom (P.triangle hk) e ≫ α.inv =
      β.hom ≫ (P.pull f).map (ε.hom ≫ e ≫ ε.inv) ≫ β.inv :=
  Functor.conjHom_conj_of_comp_eq _ α β ε h e

/-- The form of `CategoryTheory.PullbackData.conjHom_triangle_conj` for a morphism followed by the
inverse image of a morphism. -/
theorem conjHom_triangle_comp_map_conj {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k : a ⟶ c}
    (hk : f ≫ g = k) {U W : D c} {U' : D a} {V : D b} (α : (P.pull k).obj U ≅ U')
    (β : (P.pull f).obj V ≅ U') (ε : (P.pull g).obj U ≅ V)
    (h : α.inv ≫ (P.triangle hk).hom.app U = β.inv ≫ (P.pull f).map ε.inv)
    (e : (P.pull g).obj U ⟶ (P.pull g).obj W) (w : W ⟶ U) :
    α.inv ≫ Functor.conjHom (P.triangle hk) e ≫ (P.pull k).map w ≫ α.hom =
      β.inv ≫ (P.pull f).map (ε.inv ≫ e ≫ (P.pull g).map w ≫ ε.hom) ≫ β.hom := by
  have h' := P.conjHom_triangle_conj hk α.symm β.symm ε.symm h (e ≫ (P.pull g).map w)
  rw [Functor.conjHom_comp_map] at h'
  simpa only [Category.assoc, Iso.symm_hom, Iso.symm_inv] using h'

end CategoryTheory.PullbackData

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}

/-- The morphism of schemes of the site underlying a test scheme over the space of a scheme. -/
abbrev testMap {c : BigFppfOver B S hS} (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c)) :
    T.left ⟶ c :=
  yoneda.preimage T.hom.hom

/-- The structure morphism of a test scheme `T` is the image of `testMap T` under the Yoneda
embedding. -/
theorem testMap_spec {c : BigFppfOver B S hS}
    (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c)) : T.hom.hom = yoneda.map (testMap T) :=
  (yoneda.map_preimage _).symm

/-- The identification `f^*𝒪 ≅ 𝒪` is compatible with the composition comparison, at a composite. -/
theorem modulePullbackUnitIso_inv_comp_compIso_inv {P X' X : AlgebraicSpaces B S hS}
    (p : P ⟶ X') (f : X' ⟶ X) :
    (modulePullbackUnitIso B S hS (p ≫ f)).inv ≫ (modulePullbackCompIso B S hS p f).inv.app
        (SheafOfModules.unit (structureRingSheaf B S hS X)) =
      (modulePullbackUnitIso B S hS p).inv ≫
        (modulePullback B S hS p).map (modulePullbackUnitIso B S hS f).inv := by
  have h := modulePullbackUnitIso_inv_comp_triangle_hom B S hS p f (rfl : p ≫ f = p ≫ f)
  rwa [modulePullbackTriangle_rfl] at h

/-- **The identification `f^*𝒪 ≅ 𝒪` is compatible with the comparisons of the pullback
pseudofunctor datum of modules.** -/
theorem modulePullbackUnitIso_inv_comp_triangle {P X' X : AlgebraicSpaces B S hS}
    (p : P ⟶ X') (f : X' ⟶ X) {k : P ⟶ X} (hk : p ≫ f = k) :
    @CategoryStruct.comp (toposModules B S hS P) _ _ _ _ (modulePullbackUnitIso B S hS k).inv
        (((toposModulePullbackData B S hS).triangle hk).hom.app
          (SheafOfModules.unit (structureRingSheaf B S hS X))) =
      @CategoryStruct.comp (toposModules B S hS P) _ _ _ _ (modulePullbackUnitIso B S hS p).inv
        (((toposModulePullbackData B S hS).pull p).map (modulePullbackUnitIso B S hS f).inv) := by
  subst hk
  rw [PullbackData.triangle_rfl]
  exact modulePullbackUnitIso_inv_comp_compIso_inv p f

/-- **The endomorphism of `𝒪` read off a morphism into an inverse image**: for `e : f^*𝒪 ⟶ f^*M`
and `w : M ⟶ 𝒪`, the composite `𝒪 ≅ f^*𝒪 ⟶ f^*M ⟶ f^*𝒪 ≅ 𝒪`. -/
def unitCoord {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) {M : toposModules B S hS Y}
    (e : ((toposModulePullbackData B S hS).pull f).obj
        (SheafOfModules.unit (structureRingSheaf B S hS Y)) ⟶
      ((toposModulePullbackData B S hS).pull f).obj M)
    (w : M ⟶ SheafOfModules.unit (structureRingSheaf B S hS Y)) : UnitEnd X :=
  (modulePullbackUnitIsoS f).inv ≫ e ≫ ((toposModulePullbackData B S hS).pull f).map w ≫
    (modulePullbackUnitIsoS f).hom

/-- **Restriction along a composite of the endomorphism read off a morphism into an inverse image
is its inverse image**: conjugating by the comparison of the pullback pseudofunctor datum of
modules and reading off along `k = p ≫ f` is pulling back along `p` what is read off along `f`. -/
theorem unitCoord_conjHom_triangle {P X' X : AlgebraicSpaces B S hS}
    (p : P ⟶ X') (f : X' ⟶ X) {k : P ⟶ X} (hk : p ≫ f = k) {M : toposModules B S hS X}
    (e : ((toposModulePullbackData B S hS).pull f).obj
        (SheafOfModules.unit (structureRingSheaf B S hS X)) ⟶
      ((toposModulePullbackData B S hS).pull f).obj M)
    (w : M ⟶ SheafOfModules.unit (structureRingSheaf B S hS X)) :
    unitCoord k (Functor.conjHom ((toposModulePullbackData B S hS).triangle hk) e) w =
      pullEnd p (unitCoord f e w) :=
  (toposModulePullbackData B S hS).conjHom_triangle_comp_map_conj hk (modulePullbackUnitIsoS k)
    (modulePullbackUnitIsoS p) (modulePullbackUnitIsoS f)
    (modulePullbackUnitIso_inv_comp_triangle p f hk) e w

section Coordinates

attribute [local irreducible] modulePullback modulePullbackUnitIso PullbackData.triangle

variable (c : BigFppfOver B S hS) {r m : ℕ} (N : Matrix (Fin r) (Fin m) (Gam c))

/-- **The kernel functor of a matrix of functions** on the test schemes over the space of `c`. -/
abbrev matKerFunctor : (SchemesOver ((schemeSpaceFunctor B S hS).obj c))ᵒᵖ ⥤ Type (u + 1) :=
  (toposModulePullbackData B S hS).relKerFunctor (toposModulePullbackData_isCoherent B S hS)
    (schemesOverCone ((schemeSpaceFunctor B S hS).obj c))
    (SheafOfModules.unit (structureRingSheaf B S hS ((schemeSpaceFunctor B S hS).obj c)))
    (matMap c N)

variable {c N}

/-- The coordinates of a section of the kernel functor of a matrix. -/
def kerCoord (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c))
    (α : (matKerFunctor c N).obj (op T)) : Fin r → Gam T.left :=
  freePointEquiv T.left r ((modulePullbackUnitIsoS
      ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T)).inv ≫
    ((toposModulePullbackData B S hS).relKerFunctorObjEquiv
        (toposModulePullbackData_isCoherent B S hS)
      _ _ _ T α).1 ≫
    (pullFreeIso ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T) r).hom)

/-- The zero global section of `𝒪_T^n` corresponds to the zero `n`-tuple of functions. -/
theorem freePointEquiv_zero (T : BigFppfOver B S hS) (n : ℕ) :
    freePointEquiv T n 0 = 0 := by
  funext j
  change unitEndValueHom T ((0 : unitT T ⟶ freeObj (unitT T) n) ≫ biproduct.π _ j) = 0
  rw [zero_comp, map_zero]

/-- The matrix of a matrix of functions pulled back to a test scheme. -/
abbrev pulledMat (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c)) :
    Matrix (Fin r) (Fin m) (Gam T.left) :=
  N.map ((BigFppfOver.toScheme B S hS).map (testMap T)).appTop.hom

/-- The comparison of the inverse image of the morphism of a matrix with the morphism of the
pulled back matrix, at a test scheme. -/
theorem pull_matMap_eq (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c)) :
    (pullFreeIso ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T) r).inv ≫
        ((toposModulePullbackData B S hS).pull
          ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T)).map (matMap c N) ≫
        (pullFreeIso ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T) m).hom =
      matMap T.left (pulledMat (N := N) T) :=
  pullFreeIso_inv_map_matMap (T' := T.left) (T := c)
    ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T) (testMap T) (testMap_spec T) N

/-- **The coordinates of a section of the kernel functor are a solution of the pulled back
equations.** -/
theorem kerCoord_mem (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c))
    (α : (matKerFunctor c N).obj (op T)) :
    Matrix.vecMul (kerCoord T α) (pulledMat (N := N) T) = 0 := by
  let a := (toposModulePullbackData B S hS).relKerFunctorObjEquiv
      (toposModulePullbackData_isCoherent B S hS)
    _ _ _ T α
  unfold kerCoord
  rw [← freePointEquiv_comp_matMap, ← pull_matMap_eq, ← freePointEquiv_zero T.left m]
  congr 1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc a.1, a.2, zero_comp, comp_zero]

/-- A coordinate of a section of the kernel functor of a matrix, as a value of an endomorphism of
the structure sheaf. -/
theorem kerCoord_apply (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c))
    (α : (matKerFunctor c N).obj (op T)) (j : Fin r) :
    kerCoord T α j = unitEndValueHom T.left (unitCoord
      (X := (CostructuredArrow.proj (schemeSpaceFunctor B S hS)
          ((schemeSpaceFunctor B S hS).obj c) ⋙
        schemeSpaceFunctor B S hS).obj T)
      ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T)
      ((toposModulePullbackData B S hS).relKerFunctorObjEquiv
          (toposModulePullbackData_isCoherent B S hS)
        _ _ _ T α).1 (biproduct.π (fun _ : Fin r => unitT c) j)) := by
  unfold unitCoord
  change unitEndValueHom T.left (_ ≫ biproduct.π (fun _ : Fin r => unitT T.left) j) = _
  have hπ := Functor.freeObjIso_hom_π ((toposModulePullbackData B S hS).pull
    ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T))
    (modulePullbackUnitIsoS ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T)) r j
  rw [Category.assoc, Category.assoc]
  exact congrArg (fun z => unitEndValueHom T.left (_ ≫ _ ≫ z)) hπ

/-- **The coordinates of a section of the kernel functor of a matrix determine it.** -/
theorem kerCoord_injective (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c)) :
    Function.Injective (kerCoord (N := N) T) := by
  intro α β h
  have h1 := (freePointEquiv T.left r).injective h
  rw [Iso.cancel_iso_inv_left, Iso.cancel_iso_hom_right] at h1
  exact ((toposModulePullbackData B S hS).relKerFunctorObjEquiv
      (toposModulePullbackData_isCoherent B S hS)
    _ _ _ T).injective (Subtype.ext h1)

/-- **Every solution of the pulled back equations is the vector of coordinates of a section of the
kernel functor.** -/
theorem kerCoord_surjective (T : SchemesOver ((schemeSpaceFunctor B S hS).obj c))
    (v : Fin r → Gam T.left) (hv : Matrix.vecMul v (pulledMat (N := N) T) = 0) :
    ∃ α, kerCoord (N := N) T α = v := by
  let e : ((toposModulePullbackData B S hS).pull
      ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T)).obj
        (SheafOfModules.unit (structureRingSheaf B S hS ((schemeSpaceFunctor B S hS).obj c))) ≅
      unitT T.left :=
    modulePullbackUnitIsoS ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T)
  let F := pullFreeIso ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T) r
  let F' := pullFreeIso ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T) m
  let β := (freePointEquiv T.left r).symm v
  have hβ : β ≫ matMap T.left (pulledMat (N := N) T) = 0 := by
    apply (freePointEquiv T.left m).injective
    rw [freePointEquiv_comp_matMap, freePointEquiv_zero, Equiv.apply_symm_apply, hv]
  have hmat : F.inv ≫ ((toposModulePullbackData B S hS).pull
      ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T)).map (matMap c N) =
      matMap T.left (pulledMat (N := N) T) ≫ F'.inv := by
    rw [← pull_matMap_eq, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨((toposModulePullbackData B S hS).relKerFunctorObjEquiv
      (toposModulePullbackData_isCoherent B S hS)
    _ _ _ T).symm ⟨e.hom ≫ β ≫ F.inv, ?_⟩, ?_⟩
  · rw [Category.assoc, Category.assoc, hmat, ← Category.assoc β, hβ, zero_comp, comp_zero]
  · unfold kerCoord
    rw [Equiv.apply_symm_apply]
    change freePointEquiv T.left r (e.inv ≫ (e.hom ≫ β ≫ F.inv) ≫ F.hom) = v
    rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc,
      Equiv.apply_symm_apply]

/-- The value of the inverse image of an endomorphism of the structure sheaf along the morphism of
spaces of a morphism of schemes is the pullback of its value. -/
theorem unitEndValueHom_pullEnd {T' T : BigFppfOver B S hS}
    (f : (schemeSpaceFunctor B S hS).obj T' ⟶ (schemeSpaceFunctor B S hS).obj T) (g : T' ⟶ T)
    (hf : f.hom = yoneda.map g) (s : unitT T ⟶ unitT T) :
    unitEndValueHom T' (pullEnd f s) =
      ((BigFppfOver.toScheme B S hS).map g).appTop.hom (unitEndValueHom T s) := by
  have h := congrArg (fun z => unitEndValueHom T' (pullEnd f z)) (funEnd_unitEndValueHom T s)
  exact h.symm.trans ((congrArg (unitEndValueHom T') (pullEnd_funEnd f g hf _)).trans
    (unitEndValueHom_funEnd T' _))

/-- The value of the inverse image of an endomorphism of the structure sheaf along the morphism of
spaces of a morphism of test schemes is the pullback of its value. -/
theorem unitEndValueHom_pullEnd_cone {T T' : SchemesOver ((schemeSpaceFunctor B S hS).obj c)}
    (f : op T ⟶ op T') (s : unitT T.left ⟶ unitT T.left) :
    unitEndValueHom T'.left (pullEnd ((CostructuredArrow.proj (schemeSpaceFunctor B S hS)
          ((schemeSpaceFunctor B S hS).obj c) ⋙
        schemeSpaceFunctor B S hS).map f.unop) s) =
      ((BigFppfOver.toScheme B S hS).map f.unop.left).appTop.hom (unitEndValueHom T.left s) :=
  unitEndValueHom_pullEnd _ f.unop.left rfl _

/-- **Restriction of a section of the kernel functor of a matrix along a morphism of test schemes
is pullback of its coordinates.** -/
theorem kerCoord_map {T T' : SchemesOver ((schemeSpaceFunctor B S hS).obj c)} (f : op T ⟶ op T')
    (α : (matKerFunctor c N).obj (op T)) :
    kerCoord T' ((matKerFunctor c N).map f α) =
      fun j => ((BigFppfOver.toScheme B S hS).map f.unop.left).appTop.hom (kerCoord T α j) := by
  funext j
  have key := unitCoord_conjHom_triangle ((CostructuredArrow.proj (schemeSpaceFunctor B S hS)
          ((schemeSpaceFunctor B S hS).obj c) ⋙
        schemeSpaceFunctor B S hS).map f.unop)
    ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).leg T)
    ((schemesOverCone ((schemeSpaceFunctor B S hS).obj c)).w f.unop)
    ((toposModulePullbackData B S hS).relKerFunctorObjEquiv
      (toposModulePullbackData_isCoherent B S hS) _ _ _ T α).1
    (biproduct.π (fun _ : Fin r => unitT c) j)
  have e1 := PullbackData.relKerFunctorObjEquiv_map_coe (toposModulePullbackData B S hS)
    (toposModulePullbackData_isCoherent B S hS) _ _ _ f α
  rw [kerCoord_apply, kerCoord_apply]
  refine (congrArg (unitEndValueHom T'.left) ?_).trans ((unitEndValueHom_pullEnd_cone f ?s).trans
    (congrArg (fun z => ((BigFppfOver.toScheme B S hS).map f.unop.left).appTop.hom
      (unitEndValueHom T.left z)) ?_))
  · rw [e1]
    exact key
  · rfl

end Coordinates

end AlgebraicGeometry.Space

end

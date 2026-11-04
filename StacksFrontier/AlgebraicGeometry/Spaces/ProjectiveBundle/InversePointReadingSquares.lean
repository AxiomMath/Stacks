module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.InversePointReadingBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ConormalSourcePointReadingBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedClosedImmersionKernelIdealNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit

/-!
# The unit square of the inverse-line factor of the conormal source

The inverse-line factor `i_x` of the conormal source read at a scheme point `x : T ⟶ X` is
characterised by an evaluation through the identifications `R_T(x^*𝒪) ≅ 𝒪_T`.  Its base change
along `h : T' ⟶ T` (`AlgebraicGeometry.Space.inversePointReadingIso_baseChange_of_squares`) needs
that these identifications are compatible with the identification of the point readings: a
naturality square of the base change of the Zariski reading, its unit law, and Stacks 03LU at the
structure sheaf for `x ∘ h`.  This file proves those three ingredients and the paste that
combines them.

## Main results

* `CategoryTheory.Functor.unitSquare_of_squares`: the paste of the naturality, unit and triangle
  squares into the unit square.
* `AlgebraicGeometry.Space.zariskiReadingUnitHom_comp_zariskiReadingUnitIso_hom`:
  `𝒪_T ⟶ R_T 𝒪 ⟶ 𝒪_T` is the identity.
* `AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_unit_comp`: Stacks 03LU at the
  structure sheaf along a composite, and
  `AlgebraicGeometry.Space.zariskiReading_map_modulePullbackCompIso_inv_app_unit_comp`, its
  Zariski reading at `φ ≫ x`.
* `AlgebraicGeometry.Space.inversePointReadingUnitSquare_nat` and
  `AlgebraicGeometry.Space.inversePointReadingUnitSquare_unit`: the naturality and unit-law
  squares at `x`.
* `AlgebraicGeometry.Space.inversePointReadingUnitSquare_tri`: the Stacks 03LU triangle at `𝒪` for
  `x ∘ h`, in the spelling of `AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso`.
* `AlgebraicGeometry.Space.inversePointReadingUnitSquare`: the unit square of the inverse-line
  factor, the hypothesis `hUh` of
  `AlgebraicGeometry.Space.inversePointReadingIso_baseChange_of_squares`.

## Implementation notes

`AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso` writes the morphism of represented
spaces as `AlgebraicGeometry.Space.representedSpaceMap`, whose source and target are the
anonymous structures, while the Zariski reading on `T'` and the point `x ∘ h` live over
`AlgebraicGeometry.Space.yonedaSpace`.  Checking an instance of Stacks 03LU at one spelling against
the other times out, in the elaborator and in the kernel, as soon as the image of the comparison
under the Zariski reading is involved.  The triangle is therefore transported atom by atom
(`CategoryTheory.comp_comp_eq_of_heq`), each atom by a congruence lemma whose instance is cheap.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open AlgebraicGeometry.SheafOfModules (IsInvertible)

universe u

/-- **A unit square from the naturality, unit and triangle squares**: if `e : P Y ≅ R' Q₁`
intertwines `P m` with `R' n₀` (through `θ₀`), `θ₀` intertwines `P w` with `w'` (the unit law)
and `R'(c⁻¹) ≫ R'(n₀) ≫ R'(m_φ) = R'(m₀)` (the triangle), then
`(R'(c⁻¹) ≫ e⁻¹) ≫ P(m ≫ w) ≫ ν = R'(m₀) ≫ w'`. -/
theorem CategoryTheory.Functor.unitSquare_of_squares {𝒜 𝒞 𝒟 : Type*} [i𝒜 : Category 𝒜]
    [i𝒞 : Category 𝒞] [i𝒟 : Category 𝒟] (P : 𝒞 ⥤ 𝒟) (R' : 𝒜 ⥤ 𝒟) {Y Z W : 𝒞}
    {Q₀ Q₁ Q₂ Q₃ : 𝒜} {W' : 𝒟} (c : Q₁ ≅ Q₀) (e : P.obj Y ≅ R'.obj Q₁) (m : Y ≅ Z) (w : Z ≅ W)
    (ν : P.obj W ⟶ W') (θ₀ : P.obj Z ⟶ R'.obj Q₂) (n₀ : Q₁ ⟶ Q₂) (mφ : Q₂ ⟶ Q₃) (m₀ : Q₀ ≅ Q₃)
    (w' : R'.obj Q₃ ≅ W') (hnat : P.map m.hom ≫ θ₀ = e.hom ≫ R'.map n₀)
    (hunit : θ₀ ≫ R'.map mφ ≫ w'.hom = P.map w.hom ≫ ν)
    (htri : R'.map c.inv ≫ R'.map n₀ ≫ R'.map mφ = R'.map m₀.hom) :
    (R'.mapIso c.symm ≪≫ e.symm).hom ≫ P.map (m ≪≫ w).hom ≫ ν = (R'.mapIso m₀ ≪≫ w').hom := by
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, P.map_comp, Category.assoc]
  rw [← hunit, reassoc_of% hnat, Iso.inv_hom_id_assoc, reassoc_of% htri]

/-- A functor carries a composite of three morphisms equal to a fourth to the same relation
between their images. -/
theorem CategoryTheory.Functor.map_comp_comp_eq {𝒜 ℬ : Type*} [i𝒜 : Category 𝒜]
    [iℬ : Category ℬ] (F : 𝒜 ⥤ ℬ) {a b c d : 𝒜} (f : a ⟶ b) (g : b ⟶ c) (k : c ⟶ d) (m : a ⟶ d)
    (H : f ≫ g ≫ k = m) : F.map f ≫ F.map g ≫ F.map k = F.map m := by
  rw [← F.map_comp, ← F.map_comp, H]

/-- A relation `f' ≫ g' ≫ k' = m'` gives the same relation between heterogeneously equal
morphisms `f, g, k, m` with equal endpoints. -/
theorem CategoryTheory.comp_comp_eq_of_heq {𝒟 : Type*} [Category 𝒟] {A B C D A' B' C' D' : 𝒟}
    {f : A ⟶ B} {g : B ⟶ C} {k : C ⟶ D} {m : A ⟶ D} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
    {k' : C' ⟶ D'} {m' : A' ⟶ D'} (hf : HEq f f') (hg : HEq g g') (hk : HEq k k')
    (hm : HEq m m') (H : f' ≫ g' ≫ k' = m') (hA : A = A') (hB : B = B') (hC : C = C')
    (hD : D = D') : f ≫ g ≫ k = m := by
  subst hA hB hC hD
  obtain rfl := eq_of_heq hf
  obtain rfl := eq_of_heq hg
  obtain rfl := eq_of_heq hk
  obtain rfl := eq_of_heq hm
  exact H

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

section Triangle

/-- **`𝒪_T ⟶ R_T 𝒪` followed by `R_T 𝒪 ≅ 𝒪_T` is the identity**: the identification
`AlgebraicGeometry.Space.zariskiReadingUnitIso` of the Zariski reading of the structure sheaf is
the inverse of the structure map `AlgebraicGeometry.Space.zariskiReadingUnitHom`. -/
theorem zariskiReadingUnitHom_comp_zariskiReadingUnitIso_hom (T : BigFppfOver B S hS) :
    zariskiReadingUnitHom T ≫ (zariskiReadingUnitIso T).hom = 𝟙 _ :=
  (zariskiReadingUnitHomIso T).hom_inv_id


/-- The identification `g^*𝒪 ≅ 𝒪` of Stacks 03LU depends only on the morphism `g`, as a
heterogeneous equality for two spellings of it. -/
theorem modulePullbackUnitIso_hom_heq {Y Y' : AlgebraicSpaces B S hS} {g g' : Y' ⟶ Y}
    (e : g = g') :
    HEq (modulePullbackUnitIso B S hS g).hom (modulePullbackUnitIso B S hS g').hom := by
  subst e
  rfl

/-- The comparison of Stacks 03LU along `a ≫ b` depends only on `a` and on the module, as a
heterogeneous equality for two spellings of them. -/
theorem modulePullbackCompIso_app_inv_heq {Y Y₀ Y' Y'₀ Y'' : AlgebraicSpaces B S hS}
    (hY : Y = Y₀) (hY' : Y' = Y'₀) (a : Y ⟶ Y') (a' : Y₀ ⟶ Y'₀) (e : HEq a a') (b : Y' ⟶ Y'')
    (b' : Y'₀ ⟶ Y'') (hb : HEq b b') {M M' : Modules.{u, u} B S hS Y''.1 Y''.2} (hM : M = M') :
    HEq ((modulePullbackCompIso B S hS a b).app M).inv
      ((modulePullbackCompIso B S hS a' b').inv.app M') := by
  subst hY hY' hM
  obtain rfl := eq_of_heq e
  obtain rfl := eq_of_heq hb
  rfl

/-- The identification `g^*𝒪 ≅ 𝒪` of Stacks 03LU for two heterogeneously equal morphisms between
equal spaces. -/
theorem modulePullbackUnitIso_hom_heq_of_heq {Y Y₀ Y' Y'₀ : AlgebraicSpaces B S hS}
    (hY : Y = Y₀) (hY' : Y' = Y'₀) (g : Y ⟶ Y') (g' : Y₀ ⟶ Y'₀) (e : HEq g g') :
    HEq (modulePullbackUnitIso B S hS g).hom (modulePullbackUnitIso B S hS g').hom := by
  subst hY hY'
  obtain rfl := eq_of_heq e
  rfl

/-- The inverse image of a morphism of modules along two heterogeneously equal morphisms between
equal spaces. -/
theorem modulePullback_map_heq_of_heq {Y Y₀ Y' Y'₀ : AlgebraicSpaces B S hS} (hY : Y = Y₀)
    (hY' : Y' = Y'₀) (g : Y ⟶ Y') (g' : Y₀ ⟶ Y'₀) (e : HEq g g')
    {M N : Modules.{u, u} B S hS Y'.1 Y'.2} {M' N' : Modules.{u, u} B S hS Y'₀.1 Y'₀.2}
    (hM : HEq M M') (hN : HEq N N') (v : M ⟶ N) (v' : M' ⟶ N') (hv : HEq v v') :
    HEq ((modulePullback B S hS g).map v) ((modulePullback B S hS g').map v') := by
  subst hY hY'
  obtain rfl := eq_of_heq e
  obtain rfl := eq_of_heq hM
  obtain rfl := eq_of_heq hN
  obtain rfl := eq_of_heq hv
  rfl

/-- **Stacks 03LU at the structure sheaf, along a composite**: the comparison of the inverse
images along `a ≫ b` followed by the identifications `a^*b^*𝒪 ≅ a^*𝒪 ≅ 𝒪` is the identification
for `a ≫ b`. -/
theorem modulePullbackCompIso_inv_app_unit_comp {Y Y' Y'' : AlgebraicSpaces B S hS}
    (a : Y ⟶ Y') (b : Y' ⟶ Y'') :
    (modulePullbackCompIso B S hS a b).inv.app
          (SheafOfModules.unit (structureRingSheaf B S hS Y'')) ≫
        (modulePullback B S hS a).map (modulePullbackUnitIso B S hS b).hom ≫
        (modulePullbackUnitIso B S hS a).hom =
      (modulePullbackUnitIso B S hS (a ≫ b)).hom := by
  have k := modulePullbackTriangle_hom_app_unit_comp B S hS a b rfl
  rw [modulePullbackTriangle_rfl] at k
  exact k

variable (X : AlgebraicSpaces B S hS)

/-- `AlgebraicGeometry.Space.modulePullbackCompIso_inv_app_unit_comp` at a scheme point `x` and
the morphism of represented spaces of `h : T' ⟶ T`, read after the Zariski reading on `T'`. -/
theorem zariskiReading_map_modulePullbackCompIso_inv_app_unit_comp {T T' : BigFppfOver B S hS}
    (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    (zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS (yonedaSpaceMap h)
          (pointHom x)).inv.app (SheafOfModules.unit (structureRingSheaf B S hS X))) ≫
        (zariskiReadingFunctor T').map ((modulePullback B S hS (yonedaSpaceMap h)).map
          (modulePullbackUnitIso B S hS (pointHom x)).hom) ≫
        (zariskiReadingFunctor T').map (modulePullbackUnitIso B S hS (yonedaSpaceMap h)).hom =
      (zariskiReadingFunctor T').map
        (modulePullbackUnitIso B S hS (yonedaSpaceMap h ≫ pointHom x)).hom :=
  CategoryTheory.Functor.map_comp_comp_eq (ℬ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
    (iℬ := Scheme.Modules.instCategory) (zariskiReadingFunctor T') _ _ _ _
    (modulePullbackCompIso_inv_app_unit_comp (yonedaSpaceMap h) (pointHom x))

end Triangle

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.ProjectiveBundleConormal.monoidalSheafTensor

variable (X : AlgebraicSpaces B S hS) (E : SheafOfModules.{u} (structureRingSheaf B S hS X))
  (hE : E.IsQuasicoherentOnSite) (Q : InvertibleQuotient X E)

/-- The naturality square of the unit square of the inverse-line factor. -/
theorem inversePointReadingUnitSquare_nat
    [_hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L]
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          ((zariskiReadingFunctor T).mapIso (modulePullbackUnitIso B S hS (pointHom x))).hom ≫
        ((zariskiReadingPullbackHom h).app
          (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T)))) =
      (zariskiReadingPullbackIso h ((modulePullback B S hS (pointHom x)).obj
          (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
            (structureRingSheaf B S hS X).property Q.L 0))
          (isQuasicoherentOnSite_pointPullback X
            (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
              (structureRingSheaf B S hS X).property Q.L 0)
            (isQuasicoherentOnSite_invertibleTensorPower X Q.L 0) T x)).hom ≫
        (zariskiReadingFunctor T').map ((modulePullback B S hS
          (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)).map
            (modulePullbackUnitIso B S hS (pointHom x)).hom) :=
  (zariskiReadingPullbackHom h).naturality (modulePullbackUnitIso B S hS (pointHom x)).hom

/-- The unit-law square of the unit square of the inverse-line factor. -/
theorem inversePointReadingUnitSquare_unit {T T' : BigFppfOver B S hS} (h : T' ⟶ T) :
    ((zariskiReadingPullbackHom h).app
          (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T)))) ≫
        (zariskiReadingFunctor T').map (modulePullbackUnitIso B S hS
          (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)).hom ≫
        (zariskiReadingUnitIso T').hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)).map
          (zariskiReadingUnitIso T).hom ≫
        (_root_.SheafOfModules.pullbackObjUnitToUnit (RingedSpaceModuleAdjunction.structureSheafHom
          ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom)) :=
  zariskiReadingPullbackHom_app_unit_comp_inv h


/-- The comparison of Stacks 03LU along `φ_h ≫ x` at `ℒ^{⊗ 0}`, with `φ_h` the morphism of
represented spaces in the spelling of `AlgebraicGeometry.Space.pointZariskiModuleBaseChangeIso`,
is the comparison at `𝒪` with `φ_h` in the spelling of `AlgebraicGeometry.Space.yonedaSpaceMap`. -/
theorem inversePointReadingUnitSquare_compInv_heq
    [hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L]
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    HEq ((modulePullbackCompIso B S hS
        (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
        (pointHom x)).app (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L 0)).inv
      ((modulePullbackCompIso B S hS (yonedaSpaceMap h) (pointHom x)).inv.app
        (SheafOfModules.unit (structureRingSheaf B S hS X))) := by
  refine modulePullbackCompIso_app_inv_heq ?_ ?_ _ _ ?_ _ _ ?_ ?_ <;> rfl

/-- `AlgebraicGeometry.Space.inversePointReadingUnitSquare_compInv_heq` after the Zariski reading
on `T'`. -/
theorem inversePointReadingUnitSquare_map_compInv_heq
    [hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L]
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    HEq ((zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS
        (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
        (pointHom x)).app (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L 0)).inv)
      ((zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS (yonedaSpaceMap h)
        (pointHom x)).inv.app (SheafOfModules.unit (structureRingSheaf B S hS X)))) := by
  refine CategoryTheory.Functor.heq_map_of_heq _ ?_ ?_
    (inversePointReadingUnitSquare_compInv_heq X E Q x h) <;> rfl

/-- The inverse image along `φ_h` of `x^*𝒪 ≅ 𝒪`, read on `T'`, in the two spellings of `φ_h`. -/
theorem inversePointReadingUnitSquare_map_pullbackMap_heq {T T' : BigFppfOver B S hS}
    (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    HEq ((zariskiReadingFunctor T').map ((modulePullback B S hS
        (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)).map
          (modulePullbackUnitIso B S hS (pointHom x)).hom))
      ((zariskiReadingFunctor T').map ((modulePullback B S hS (yonedaSpaceMap h)).map
        (modulePullbackUnitIso B S hS (pointHom x)).hom)) := by
  refine CategoryTheory.Functor.heq_map_of_heq _ ?_ ?_
    (modulePullback_map_heq_of_heq ?_ ?_ _ _ ?_ ?_ ?_ _ _ ?_) <;> rfl

/-- The identification `φ_h^*𝒪 ≅ 𝒪`, read on `T'`, in the two spellings of `φ_h`. -/
theorem inversePointReadingUnitSquare_map_unitIso_heq {T T' : BigFppfOver B S hS}
    (h : T' ⟶ T) :
    HEq ((zariskiReadingFunctor T').map (modulePullbackUnitIso B S hS
        (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)).hom)
      ((zariskiReadingFunctor T').map (modulePullbackUnitIso B S hS (yonedaSpaceMap h)).hom) := by
  refine CategoryTheory.Functor.heq_map_of_heq _ ?_ ?_
    (modulePullbackUnitIso_hom_heq_of_heq rfl rfl _ _ HEq.rfl) <;> rfl

/-- **The Stacks 03LU triangle of the unit square of the inverse-line factor**: the comparison of
the inverse images along `x ∘ h` at `ℒ^{⊗ 0} = 𝒪`, followed by `φ_h^*(x^*𝒪 ≅ 𝒪)` and
`φ_h^*𝒪 ≅ 𝒪`, is `(x ∘ h)^*𝒪 ≅ 𝒪`, read on `T'`. -/
theorem inversePointReadingUnitSquare_tri
    [hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L]
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    (zariskiReadingFunctor T').map ((modulePullbackCompIso B S hS
          (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
          (pointHom x)).app (Stacks.SheafOfModules.Invertible.tensorPower
            (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L 0)).inv ≫
        (zariskiReadingFunctor T').map ((modulePullback B S hS
          (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)).map
            (modulePullbackUnitIso B S hS (pointHom x)).hom) ≫
        (zariskiReadingFunctor T').map (modulePullbackUnitIso B S hS
          (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)).hom =
      (zariskiReadingFunctor T').map
        (modulePullbackUnitIso B S hS (pointHom (yoneda.map h ≫ x))).hom :=
  CategoryTheory.comp_comp_eq_of_heq (inversePointReadingUnitSquare_map_compInv_heq X E Q x h)
    (inversePointReadingUnitSquare_map_pullbackMap_heq X x h)
    (inversePointReadingUnitSquare_map_unitIso_heq h) HEq.rfl
    (zariskiReading_map_modulePullbackCompIso_inv_app_unit_comp X x h) rfl rfl rfl rfl

/-- **The unit square of the inverse-line factor**: the identification of the point readings of
`ℒ^{⊗ 0}` at `x ∘ h` and at `x`, followed by `τ^*` of `R_T(x^*𝒪) ≅ 𝒪_T` and `τ^*𝒪_T ≅ 𝒪_{T'}`,
is `R_{T'}((x ∘ h)^*𝒪) ≅ 𝒪_{T'}`. -/
theorem inversePointReadingUnitSquare
    [hQ : IsInvertible (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L]
    {T T' : BigFppfOver B S hS} (x : yoneda.obj T ⟶ X.1) (h : T' ⟶ T) :
    CategoryTheory.Functor.BaseChangeUnitSquare
      (𝒞₀ := ((BigFppfOver.toScheme B S hS).obj T).Modules)
      (𝒞₁ := ((BigFppfOver.toScheme B S hS).obj T').Modules)
      (i₀ := Scheme.Modules.instCategory) (i₁ := Scheme.Modules.instCategory)
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h))
      (pointZariskiModuleBaseChangeIso X _ (isQuasicoherentOnSite_invertibleTensorPower X Q.L 0)
        x h).hom
      ((zariskiReadingFunctor T).mapIso (modulePullbackUnitIso B S hS (pointHom x)) ≪≫
        zariskiReadingUnitIso T)
      ((zariskiReadingFunctor T').mapIso
          (modulePullbackUnitIso B S hS (pointHom (yoneda.map h ≫ x))) ≪≫
        zariskiReadingUnitIso T')
      (_root_.SheafOfModules.pullbackObjUnitToUnit (RingedSpaceModuleAdjunction.structureSheafHom
        ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom)) :=
  CategoryTheory.Functor.unitSquare_of_squares
    (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map h)) (zariskiReadingFunctor T')
    ((modulePullbackCompIso B S hS
        (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)
        (pointHom x)).app (Stacks.SheafOfModules.Invertible.tensorPower
          (structureCommRings B S hS X) (structureRingSheaf B S hS X).property Q.L 0))
    (zariskiReadingPullbackIso h ((modulePullback B S hS (pointHom x)).obj
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L 0))
      (isQuasicoherentOnSite_pointPullback X
        (Stacks.SheafOfModules.Invertible.tensorPower (structureCommRings B S hS X)
          (structureRingSheaf B S hS X).property Q.L 0)
        (isQuasicoherentOnSite_invertibleTensorPower X Q.L 0) T x))
    ((zariskiReadingFunctor T).mapIso (modulePullbackUnitIso B S hS (pointHom x)))
    (zariskiReadingUnitIso T)
    (_root_.SheafOfModules.pullbackObjUnitToUnit (RingedSpaceModuleAdjunction.structureSheafHom
      ((BigFppfOver.toScheme B S hS).map h).toLRSHom.toShHom))
    ((zariskiReadingPullbackHom h).app
      (SheafOfModules.unit (structureRingSheaf B S hS (yonedaSpace B S hS T))))
    ((modulePullback B S hS
        (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)).map
      (modulePullbackUnitIso B S hS (pointHom x)).hom)
    ((modulePullbackUnitIso B S hS
      (representedSpaceMap B S hS h : yonedaSpace B S hS T' ⟶ yonedaSpace B S hS T)).hom)
    (modulePullbackUnitIso B S hS (pointHom (yoneda.map h ≫ x))) (zariskiReadingUnitIso T')
    (inversePointReadingUnitSquare_nat X E Q x h) (inversePointReadingUnitSquare_unit h)
    (inversePointReadingUnitSquare_tri X E Q x h)

end AlgebraicGeometry.Space

end

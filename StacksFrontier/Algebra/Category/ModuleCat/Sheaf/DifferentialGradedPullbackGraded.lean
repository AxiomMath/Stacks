module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedPullback

/-!
# The pullback of right differential graded modules, on the underlying graded modules

Let `f` be a morphism of ringed sites and let `φ : A' ⟶ f_*A` be a semilinear homomorphism of
sheaves of differential graded algebras. A pullback `f^*` of right differential graded
`A'`-modules is given by a universal property which tests only *morphisms of differential graded
modules* out of `f^*M`. This file shows that the same datum transports homomorphisms of the
*underlying graded* modules, which do not commute with the differentials: a homomorphism
`r : M → N` of the graded modules underlying two right differential graded `A'`-modules has a
unique transport `f^*r : f^*M → f^*N` compatible with the units of the two pullbacks, and the
transport is a functor, additive, and agrees with `f^*` on morphisms of differential graded
modules.

## Main definitions

* `SheafOfModules.Cofree.semilinearMap` is the semilinear map of cofree differential graded
  modules induced by a semilinear map of right differential graded modules.
* `SheafOfModules.DifferentialGradedModule.PullbackData.gradedMap` is the transport of a
  homomorphism of the underlying graded modules along a pullback.

## Main results

* `SheafOfModules.DifferentialGradedModule.PullbackData.gradedMap_unit`: the transport is
  compatible with the units of the two pullbacks, and
  `SheafOfModules.DifferentialGradedModule.PullbackData.graded_hom_ext`: that compatibility
  determines it.
* `SheafOfModules.DifferentialGradedModule.PullbackData.gradedMap_id`, `gradedMap_comp`,
  `gradedMap_add` and `gradedMap_forget`: the transport preserves identities, composition and
  sums, and carries the underlying homomorphism of a morphism of right differential graded
  modules to the underlying homomorphism of its pullback.

## Implementation notes

The universal property of a `PullbackData` concerns morphisms of differential graded modules
only, so a homomorphism of the underlying graded modules cannot be transported by applying the
pullback functor to it. What makes the transport possible is the cofree differential graded
module `Cofree.cofree N` on a graded module `N`: a homomorphism of graded modules `M → N` is
the same thing as a morphism of differential graded modules `M ⟶ Cofree.cofree N`, so the graded
homomorphisms out of `f^*M` are the differential graded morphisms out of `f^*M` into one cofree
test object and the degree-zero universal property reaches them.

Only one further ingredient is needed, `Cofree.semilinearMap`: a semilinear map `θ : Z ⟶ Y`
induces a semilinear map of the cofree modules on the underlying graded modules, applying `θ` in
each of the two coordinates of `Cofree.piece N n = Nⁿ ⊕ Nⁿ⁺¹`. Commutation with the differential
is automatic there, the differential of a cofree module being `(x, y) ↦ (y, 0)`, and the
compatibility with the action uses that `φ` commutes with the differentials of the two algebras,
which is exactly where the signed Leibniz term of the cofree action is matched.

Neither continuity of the underlying functor of sites nor the direct image appears: the
transport is available for an arbitrary morphism of ringed sites, as the pullback itself is. The
cofree module is taken on the *unshifted* underlying graded module, so the transport is of
homomorphisms of degree zero; nothing below needs the homogeneous maps of other degrees.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FRJ](https://stacks.math.columbia.edu/tag/0FRJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a a' m m' v u v' u'

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}
  {C' : Type u'} [Category.{v'} C'] {J' : GrothendieckTopology C'} {R' : Sheaf J' RingCat.{t}}
  {u : C' ⥤ C} {σ : R'.obj ⟶ u.op ⋙ R.obj} {A : DifferentialGradedAlgebra.{t, a} R}
  {A' : DifferentialGradedAlgebra.{t, a'} R'}
  {φ : DifferentialGradedAlgebra.SemilinearHom u σ A' A}

namespace DifferentialGradedModule

/-- A semilinear map of right differential graded modules commutes with transport along an
equality of degrees. -/
theorem SemilinearHom.app_castHom {Z : DifferentialGradedModule.{t, a', m'} A'}
    {Y : DifferentialGradedModule.{t, a, m} A} (θ : SemilinearHom φ Z Y) {k k' : ℤ} (h : k = k')
    (V : C'ᵒᵖ) (x : (Z.complex.X k).val.obj V) :
    θ.app k' V (castHom Z.complex.X h V x) =
      castHom Y.complex.X h (u.op.obj V) (θ.app k V x) := by
  subst h; rfl

/-- The differential of a cofree differential graded module, in the shape in which the
coordinate lemmas state it. -/
theorem cofree_complex_d (N : GradedModule.{t, a, m} A.toGradedAlgebra) (k : ℤ) :
    (Cofree.cofree N).complex.d k (k + 1) = Cofree.d N k :=
  CochainComplex.of_d _ _ k

section GradedComponents

variable {Z : DifferentialGradedModule.{t, a', m'} A'} {Y : DifferentialGradedModule.{t, a, m} A}
  (θ : SemilinearHom φ Z Y)

/-- The components of a semilinear map of right differential graded modules, read as maps of the
homogeneous pieces of the underlying graded modules. -/
def SemilinearHom.gradedApp (n : ℤ) (V : C'ᵒᵖ) :
    (((forgetToGradedModule A').obj Z).piece n).val.obj V →+
      (((forgetToGradedModule A).obj Y).piece n).val.obj (u.op.obj V) :=
  θ.app n V

/-- The graded components of `θ` agree with its components. -/
theorem SemilinearHom.gradedApp_apply (n : ℤ) (V : C'ᵒᵖ)
    (x : (((forgetToGradedModule A').obj Z).piece n).val.obj V) :
    θ.gradedApp n V x = θ.app n V x :=
  rfl

/-- The graded components of `θ` are semilinear along `σ`. -/
theorem SemilinearHom.gradedApp_smul (n : ℤ) (V : C'ᵒᵖ) (s : R'.obj.obj V)
    (x : (((forgetToGradedModule A').obj Z).piece n).val.obj V) :
    θ.gradedApp n V (s • x) = (σ.app V).hom s • θ.gradedApp n V x :=
  θ.map_smul n V s x

/-- The graded components of `θ` commute with restriction of sections. -/
theorem SemilinearHom.gradedApp_restrict (n : ℤ) {V W : C'ᵒᵖ} (k : V ⟶ W)
    (x : (((forgetToGradedModule A').obj Z).piece n).val.obj V) :
    θ.gradedApp n W ((((forgetToGradedModule A').obj Z).piece n).val.map k x) =
      (((forgetToGradedModule A).obj Y).piece n).val.map (u.op.map k) (θ.gradedApp n V x) :=
  θ.naturality n k x

/-- The graded components of `θ` carry the right action of `A'` to the right action of `A`
along `φ`. -/
theorem SemilinearHom.gradedApp_smul_algebra (n i : ℤ) (V : C'ᵒᵖ)
    (x : (((forgetToGradedModule A').obj Z).piece n).val.obj V)
    (b : (A'.complex.X i).val.obj V) :
    θ.gradedApp (n + i) V (((forgetToGradedModule A').obj Z).smul n i V x b) =
      ((forgetToGradedModule A).obj Y).smul n i (u.op.obj V) (θ.gradedApp n V x)
        (φ.app i V b) :=
  θ.map_mul n i V x b

/-- The graded components of `θ` commute with transport along an equality of degrees. -/
theorem SemilinearHom.gradedApp_castHom {k k' : ℤ} (h : k = k') (V : C'ᵒᵖ)
    (x : (((forgetToGradedModule A').obj Z).piece k).val.obj V) :
    θ.gradedApp k' V (castHom ((forgetToGradedModule A').obj Z).piece h V x) =
      castHom ((forgetToGradedModule A).obj Y).piece h (u.op.obj V) (θ.gradedApp k V x) := by
  subst h; rfl

/-- The graded components of `θ` commute with the differentials. -/
theorem SemilinearHom.gradedApp_comm_d (n : ℤ) (V : C'ᵒᵖ)
    (x : (((forgetToGradedModule A').obj Z).piece n).val.obj V) :
    θ.gradedApp (n + 1) V (homSections (Z.complex.d n (n + 1)) V x) =
      homSections (Y.complex.d n (n + 1)) (u.op.obj V) (θ.gradedApp n V x) :=
  θ.comm_d n V x

/-- The differential of `Y` applied after `θ` equals `θ` applied after the differential of
`Z`. -/
theorem SemilinearHom.homSections_comm_d (n : ℤ) (V : C'ᵒᵖ)
    (x : (((forgetToGradedModule A').obj Z).piece n).val.obj V) :
    homSections (Y.complex.d n (n + 1)) (u.op.obj V) (θ.app n V x) =
      θ.app (n + 1) V (homSections (Z.complex.d n (n + 1)) V x) :=
  (θ.comm_d n V x).symm

end GradedComponents

end DifferentialGradedModule

/-- A semilinear homomorphism of sheaves of differential graded algebras commutes with the
differential, in the shape in which the action on a cofree module states it. -/
theorem DifferentialGradedAlgebra.SemilinearHom.cofree_algD (i : ℤ) (V : C'ᵒᵖ)
    (b : (A'.complex.X i).val.obj V) :
    φ.app (i + 1) V (Cofree.algD i V b) = Cofree.algD i (u.op.obj V) (φ.app i V b) :=
  φ.comm_d i V b

namespace Cofree

open DifferentialGradedModule

section Coordinates

universe tc ac mc vc uc

variable {Cc : Type uc} [Category.{vc} Cc] {Jc : GrothendieckTopology Cc}
  {Rc : Sheaf Jc RingCat.{tc}} {Ac : DifferentialGradedAlgebra.{tc, ac} Rc}
  (N : GradedModule.{tc, ac, mc} Ac.toGradedAlgebra)

/-- The first coordinate of the inclusion of the first summand is the identity. -/
@[simp] theorem coordFst_coordInl (k : ℤ) (U : Ccᵒᵖ) (x : (N.piece k).val.obj U) :
    coordFst N k U (coordInl N k U x) = x :=
  biprodFst_inl _ _ _ _

/-- The first coordinate of the inclusion of the second summand is zero. -/
@[simp] theorem coordFst_coordInr (k : ℤ) (U : Ccᵒᵖ) (y : (N.piece (k + 1)).val.obj U) :
    coordFst N k U (coordInr N k U y) = 0 :=
  biprodFst_inr _ _ _ _

/-- The second coordinate of the inclusion of the first summand is zero. -/
@[simp] theorem coordSnd_coordInl (k : ℤ) (U : Ccᵒᵖ) (x : (N.piece k).val.obj U) :
    coordSnd N k U (coordInl N k U x) = 0 :=
  biprodSnd_inl _ _ _ _

/-- The second coordinate of the inclusion of the second summand is the identity. -/
@[simp] theorem coordSnd_coordInr (k : ℤ) (U : Ccᵒᵖ) (y : (N.piece (k + 1)).val.obj U) :
    coordSnd N k U (coordInr N k U y) = y :=
  biprodSnd_inr _ _ _ _

/-- The differential of a cofree differential graded module on local sections, in the vocabulary
of the homogeneous pieces. -/
theorem homSections_cofree_complex_d (k : ℤ) (U : Ccᵒᵖ) (x : (piece N k).val.obj U) :
    homSections ((Cofree.cofree N).complex.d k (k + 1)) U x = homSections (d N k) U x :=
  homSections_congr (CochainComplex.of_d _ _ k) U x

end Coordinates

section CofreeHom

universe th ah mh vh uh

variable {Ch : Type uh} [Category.{vh} Ch] {Jh : GrothendieckTopology Ch}
  {Rh : Sheaf Jh RingCat.{th}} {Ah : DifferentialGradedAlgebra.{th, ah} Rh}
  {M : DifferentialGradedModule.{th, ah, mh} Ah}
  (N : GradedModule.{th, ah, mh} Ah.toGradedAlgebra)

/-- The first coordinate of the cofree lift of a graded homomorphism is the homomorphism. -/
theorem coordFst_liftHom (α : (forgetToGradedModule Ah).obj M ⟶ N) (n : ℤ) (U : Chᵒᵖ)
    (z : (((forgetToGradedModule Ah).obj M).piece n).val.obj U) :
    coordFst N n U (homSections (liftHom N α n) U z) = homSections (α.app n) U z :=
  coordFst_lift N n _ _ U z

/-- The second coordinate of the cofree lift of a graded homomorphism is the homomorphism
applied after the differential. -/
theorem coordSnd_liftHom (α : (forgetToGradedModule Ah).obj M ⟶ N) (n : ℤ) (U : Chᵒᵖ)
    (z : (((forgetToGradedModule Ah).obj M).piece n).val.obj U) :
    coordSnd N n U (homSections (liftHom N α n) U z) =
      homSections (α.app (n + 1)) U (homSections (M.complex.d n (n + 1)) U z) :=
  coordSnd_lift N n _ _ U z

/-- The graded homomorphism attached to a morphism into a cofree module, on local sections. -/
theorem homSections_lowerHom_app (ψ : M ⟶ Cofree.cofree N) (n : ℤ) (U : Chᵒᵖ)
    (z : (((forgetToGradedModule Ah).obj M).piece n).val.obj U) :
    homSections ((lowerHom N ψ).app n) U z =
      coordFst N n U (homSections (ψ.toHomologicalComplex.f n) U z) :=
  rfl

end CofreeHom

section GradedSemilinear

variable {G : GradedModule.{t, a', m'} A'.toGradedAlgebra}
  {G' : GradedModule.{t, a, m} A.toGradedAlgebra}
  (τ : ∀ (n : ℤ) (V : C'ᵒᵖ), (G.piece n).val.obj V →+ (G'.piece n).val.obj (u.op.obj V))

/-- The two-coordinate map on sections of the cofree modules induced by a degreewise map from
the pieces of a graded module on the target site to the pieces of one on the source site. -/
noncomputable def gradedSemilinearApp (n : ℤ) (V : C'ᵒᵖ) :
    (piece G n).val.obj V →+ (piece G' n).val.obj (u.op.obj V) :=
  (coordInl G' n (u.op.obj V)).comp ((τ n V).comp (coordFst G n V))
    + (coordInr G' n (u.op.obj V)).comp ((τ (n + 1) V).comp (coordSnd G n V))

/-- `gradedSemilinearApp τ` applies `τ` in each of the two coordinates. -/
theorem gradedSemilinearApp_apply (n : ℤ) (V : C'ᵒᵖ) (ξ : (piece G n).val.obj V) :
    gradedSemilinearApp τ n V ξ =
      coordInl G' n (u.op.obj V) (τ n V (coordFst G n V ξ))
        + coordInr G' n (u.op.obj V) (τ (n + 1) V (coordSnd G n V ξ)) :=
  rfl

/-- The first coordinate of `gradedSemilinearApp τ` is `τ` applied to the first coordinate. -/
@[simp] theorem coordFst_gradedSemilinearApp (n : ℤ) (V : C'ᵒᵖ) (ξ : (piece G n).val.obj V) :
    coordFst G' n (u.op.obj V) (gradedSemilinearApp τ n V ξ) = τ n V (coordFst G n V ξ) := by
  rw [gradedSemilinearApp_apply, map_add, coordFst_coordInl, coordFst_coordInr, add_zero]

/-- The second coordinate of `gradedSemilinearApp τ` is `τ` applied to the second
coordinate. -/
@[simp] theorem coordSnd_gradedSemilinearApp (n : ℤ) (V : C'ᵒᵖ) (ξ : (piece G n).val.obj V) :
    coordSnd G' n (u.op.obj V) (gradedSemilinearApp τ n V ξ) =
      τ (n + 1) V (coordSnd G n V ξ) := by
  rw [gradedSemilinearApp_apply, map_add, coordSnd_coordInl, coordSnd_coordInr, zero_add]

/-- A degreewise map of the pieces of two graded modules commutes with transport along an
equality of degrees. -/
theorem gradedSemilinear_castHom {k k' : ℤ} (h : k = k') (V : C'ᵒᵖ)
    (y : (G.piece k).val.obj V) :
    τ k' V (castHom G.piece h V y) = castHom G'.piece h (u.op.obj V) (τ k V y) := by
  subst h; rfl

/-- **A degreewise semilinear map of graded modules induces a semilinear map of the cofree
differential graded modules on them**: it applies the given map in each of the two coordinates.
Commutation with the differentials is automatic, the differential of a cofree module being the
shift of the second coordinate into the first, and the compatibility with the cofree action uses
that `φ` commutes with the differentials of the two algebras. -/
noncomputable def gradedSemilinearMap
    (hsmul : ∀ (n : ℤ) (V : C'ᵒᵖ) (s : R'.obj.obj V) (x : (G.piece n).val.obj V),
      τ n V (s • x) = (σ.app V).hom s • τ n V x)
    (hnat : ∀ (n : ℤ) {V W : C'ᵒᵖ} (k : V ⟶ W) (x : (G.piece n).val.obj V),
      τ n W ((G.piece n).val.map k x) = (G'.piece n).val.map (u.op.map k) (τ n V x))
    (hmul : ∀ (n i : ℤ) (V : C'ᵒᵖ) (x : (G.piece n).val.obj V)
        (b : (A'.complex.X i).val.obj V),
      τ (n + i) V (G.smul n i V x b) = G'.smul n i (u.op.obj V) (τ n V x) (φ.app i V b)) :
    SemilinearHom φ (Cofree.cofree G) (Cofree.cofree G') where
  app n V := gradedSemilinearApp τ n V
  map_smul n V s x := by
    revert x
    change ∀ x : (piece G n).val.obj V,
      gradedSemilinearApp τ n V (s • x) = (σ.app V).hom s • gradedSemilinearApp τ n V x
    intro x
    refine sections_ext G' (u.op.obj V) ?_ ?_
    · rw [coordFst_gradedSemilinearApp, coordFst_smul, hsmul, coordFst_smul,
        coordFst_gradedSemilinearApp]
    · rw [coordSnd_gradedSemilinearApp, coordSnd_smul, hsmul, coordSnd_smul,
        coordSnd_gradedSemilinearApp]
  naturality n {V W} k x := by
    revert x
    change ∀ x : (piece G n).val.obj V,
      gradedSemilinearApp τ n W ((piece G n).val.map k x) =
        (piece G' n).val.map (u.op.map k) (gradedSemilinearApp τ n V x)
    intro x
    refine sections_ext G' (u.op.obj W) ?_ ?_
    · rw [coordFst_gradedSemilinearApp τ n W ((piece G n).val.map k x),
        coordFst_map, hnat, coordFst_map, coordFst_gradedSemilinearApp]
    · rw [coordSnd_gradedSemilinearApp τ n W ((piece G n).val.map k x),
        coordSnd_map, hnat, coordSnd_map, coordSnd_gradedSemilinearApp]
  comm_d n V x := by
    revert x
    change ∀ x : (piece G n).val.obj V,
      gradedSemilinearApp τ (n + 1) V
          (homSections ((Cofree.cofree G).complex.d n (n + 1)) V x) =
        homSections ((Cofree.cofree G').complex.d n (n + 1)) (u.op.obj V)
          (gradedSemilinearApp τ n V x)
    intro x
    rw [homSections_cofree_complex_d G n V x,
      homSections_cofree_complex_d G' n (u.op.obj V) (gradedSemilinearApp τ n V x)]
    refine sections_ext G' (u.op.obj V) ?_ ?_
    · rw [coordFst_gradedSemilinearApp τ (n + 1) V (homSections (Cofree.d G n) V x),
        coordFst_d, coordFst_d, coordSnd_gradedSemilinearApp]
    · rw [coordSnd_gradedSemilinearApp τ (n + 1) V (homSections (Cofree.d G n) V x),
        coordSnd_d, coordSnd_d, map_zero]
  map_mul n i V x b := by
    revert x
    change ∀ x : (piece G n).val.obj V,
      gradedSemilinearApp τ (n + i) V (mulHom G n i V b x) =
        mulHom G' n i (u.op.obj V) (φ.app i V b) (gradedSemilinearApp τ n V x)
    intro x
    refine sections_ext G' (u.op.obj V) ?_ ?_
    · rw [coordFst_gradedSemilinearApp, coordFst_mulHom, coordFst_mulHom,
        coordFst_gradedSemilinearApp, hmul]
    · rw [coordSnd_gradedSemilinearApp, coordSnd_mulHom, coordSnd_mulHom,
        coordFst_gradedSemilinearApp, coordSnd_gradedSemilinearApp, map_add, map_zsmul,
        gradedSemilinear_castHom τ (add_right_comm n 1 i),
        gradedSemilinear_castHom τ (add_assoc n i 1).symm, hmul, hmul, φ.cofree_algD]

end GradedSemilinear

variable {Z : DifferentialGradedModule.{t, a', m'} A'} {Y : DifferentialGradedModule.{t, a, m} A}

/-- The two-coordinate map on sections of the cofree modules induced by a semilinear map of
right differential graded modules. -/
noncomputable def semilinearApp (θ : SemilinearHom φ Z Y) (n : ℤ) (V : C'ᵒᵖ) :
    (piece ((forgetToGradedModule A').obj Z) n).val.obj V →+
      (piece ((forgetToGradedModule A).obj Y) n).val.obj (u.op.obj V) :=
  gradedSemilinearApp (fun p W => θ.gradedApp p W) n V

/-- `semilinearApp θ` applies `θ` in each of the two coordinates. -/
theorem semilinearApp_apply (θ : SemilinearHom φ Z Y) (n : ℤ) (V : C'ᵒᵖ)
    (ξ : (piece ((forgetToGradedModule A').obj Z) n).val.obj V) :
    semilinearApp θ n V ξ =
      coordInl ((forgetToGradedModule A).obj Y) n (u.op.obj V)
          (θ.gradedApp n V (coordFst ((forgetToGradedModule A').obj Z) n V ξ))
        + coordInr ((forgetToGradedModule A).obj Y) n (u.op.obj V)
          (θ.gradedApp (n + 1) V (coordSnd ((forgetToGradedModule A').obj Z) n V ξ)) :=
  rfl

/-- The first coordinate of `semilinearApp θ` is `θ` applied to the first coordinate. -/
@[simp] theorem coordFst_semilinearApp (θ : SemilinearHom φ Z Y) (n : ℤ) (V : C'ᵒᵖ)
    (ξ : (piece ((forgetToGradedModule A').obj Z) n).val.obj V) :
    coordFst ((forgetToGradedModule A).obj Y) n (u.op.obj V) (semilinearApp θ n V ξ) =
      θ.gradedApp n V (coordFst ((forgetToGradedModule A').obj Z) n V ξ) :=
  coordFst_gradedSemilinearApp _ n V ξ

/-- The second coordinate of `semilinearApp θ` is `θ` applied to the second coordinate. -/
@[simp] theorem coordSnd_semilinearApp (θ : SemilinearHom φ Z Y) (n : ℤ) (V : C'ᵒᵖ)
    (ξ : (piece ((forgetToGradedModule A').obj Z) n).val.obj V) :
    coordSnd ((forgetToGradedModule A).obj Y) n (u.op.obj V) (semilinearApp θ n V ξ) =
      θ.gradedApp (n + 1) V (coordSnd ((forgetToGradedModule A').obj Z) n V ξ) :=
  coordSnd_gradedSemilinearApp _ n V ξ

/-- **A semilinear map of right differential graded modules induces one of the cofree modules on
the underlying graded modules**: it applies the given map in each of the two coordinates.
Commutation with the differentials is automatic, the differential of a cofree module being the
shift of the second coordinate into the first. -/
noncomputable def semilinearMap (θ : SemilinearHom φ Z Y) :
    SemilinearHom φ (Cofree.cofree ((forgetToGradedModule A').obj Z))
      (Cofree.cofree ((forgetToGradedModule A).obj Y)) :=
  gradedSemilinearMap (fun p W => θ.gradedApp p W) (fun p W => θ.gradedApp_smul p W)
    (fun p _ _ k => θ.gradedApp_restrict p k) fun p i W => θ.gradedApp_smul_algebra p i W

end Cofree

namespace DifferentialGradedModule

namespace PullbackData

variable (PD : PullbackData.{t, a, m, v, u, a', m', v', u'} φ)
  {W Z : DifferentialGradedModule.{t, a', m'} A'}

/-- **The transport of a homomorphism of the underlying graded modules along a pullback**: the
unique homomorphism of the graded modules underlying the two pullbacks which is compatible with
the units. -/
noncomputable def gradedMap
    (r : (forgetToGradedModule A').obj W ⟶ (forgetToGradedModule A').obj Z) :
    (forgetToGradedModule A).obj (PD.obj W) ⟶ (forgetToGradedModule A).obj (PD.obj Z) :=
  Cofree.lowerHom _ ((PD.isPullback W).desc
    ((Cofree.semilinearMap (PD.unit Z)).precomp (Cofree.liftDgHom _ r)))

/-- Equal semilinear maps have equal components. -/
private theorem app_congr_hom {W : DifferentialGradedModule.{t, a', m'} A'}
    {Z : DifferentialGradedModule.{t, a, m} A}
    {θ ϑ : SemilinearHom φ W Z} (h : θ = ϑ) (i : ℤ) (V : C'ᵒᵖ)
    (x : (W.complex.X i).val.obj V) : θ.app i V x = ϑ.app i V x := by
  subst h; rfl

/-- **The transport is compatible with the units of the two pullbacks.** -/
theorem gradedMap_unit
    (r : (forgetToGradedModule A').obj W ⟶ (forgetToGradedModule A').obj Z) (i : ℤ)
    (V : C'ᵒᵖ) (x : (((forgetToGradedModule A').obj W).piece i).val.obj V) :
    homSections ((PD.gradedMap r).app i) (u.op.obj V) ((PD.unit W).app i V x) =
      (PD.unit Z).app i V (homSections (r.app i) V x) := by
  have hfac := app_congr_hom ((PD.isPullback W).fac ((Cofree.semilinearMap (PD.unit Z)).precomp
    (Cofree.liftDgHom ((forgetToGradedModule A').obj Z) r))) i V x
  refine (Cofree.homSections_lowerHom_app _ _ i _ _).trans ?_
  erw [hfac, Cofree.coordFst_semilinearApp]
  exact congrArg _ (Cofree.coordFst_liftHom _ r i V x)

/-- **The compatibility with the units determines a homomorphism of the graded modules
underlying the pullbacks.** -/
theorem graded_hom_ext {G : GradedModule.{t, a, m} A.toGradedAlgebra}
    {α β : (forgetToGradedModule A).obj (PD.obj W) ⟶ G}
    (h : ∀ (i : ℤ) (V : C'ᵒᵖ) (x : (((forgetToGradedModule A').obj W).piece i).val.obj V),
      homSections (α.app i) (u.op.obj V) ((PD.unit W).app i V x) =
        homSections (β.app i) (u.op.obj V) ((PD.unit W).app i V x)) :
    α = β := by
  have key : Cofree.liftDgHom G α = Cofree.liftDgHom G β := by
    refine (PD.isPullback W).hom_ext (SemilinearHom.ext fun i V x => ?_)
    show homSections (Cofree.liftHom G α i)
        (u.op.obj V) ((PD.unit W).app i V x) =
      homSections (Cofree.liftHom G β i)
        (u.op.obj V) ((PD.unit W).app i V x)
    refine Cofree.sections_ext G (u.op.obj V) ?_ ?_
    · rw [Cofree.coordFst_liftHom _ α i (u.op.obj V) ((PD.unit W).app i V x),
        Cofree.coordFst_liftHom _ β i (u.op.obj V) ((PD.unit W).app i V x)]
      exact h i V x
    · rw [Cofree.coordSnd_liftHom _ α i (u.op.obj V) ((PD.unit W).app i V x),
        Cofree.coordSnd_liftHom _ β i (u.op.obj V) ((PD.unit W).app i V x),
        (PD.unit W).homSections_comm_d i V x]
      exact h (i + 1) V _
  calc α = Cofree.lowerHom _ (Cofree.liftDgHom _ α) := (Cofree.lowerHom_liftDgHom _ α).symm
    _ = Cofree.lowerHom _ (Cofree.liftDgHom _ β) := congrArg _ key
    _ = β := Cofree.lowerHom_liftDgHom _ β

/-- The transport of the underlying homomorphism of a morphism of right differential graded
modules is the underlying homomorphism of its pullback. -/
theorem gradedMap_forget (h : W ⟶ Z) :
    PD.gradedMap ((forgetToGradedModule A').map h) =
      (forgetToGradedModule A).map (PD.map h) := by
  refine PD.graded_hom_ext fun i V x => ?_
  rw [PD.gradedMap_unit]
  exact (app_congr_hom (PD.unit_postcomp_map h) i V x).symm

/-- The transport of the identity is the identity. -/
theorem gradedMap_id : PD.gradedMap (𝟙 ((forgetToGradedModule A').obj W)) = 𝟙 _ := by
  refine PD.graded_hom_ext fun i V x => ?_
  rw [PD.gradedMap_unit]
  rfl

/-- The transport of a composite is the composite of the transports. -/
theorem gradedMap_comp {X : DifferentialGradedModule.{t, a', m'} A'}
    (r : (forgetToGradedModule A').obj W ⟶ (forgetToGradedModule A').obj Z)
    (r' : (forgetToGradedModule A').obj Z ⟶ (forgetToGradedModule A').obj X) :
    PD.gradedMap (r ≫ r') = PD.gradedMap r ≫ PD.gradedMap r' := by
  refine PD.graded_hom_ext fun i V x => ?_
  show homSections ((PD.gradedMap (r ≫ r')).app i) (u.op.obj V) ((PD.unit W).app i V x) =
    homSections ((PD.gradedMap r').app i) (u.op.obj V)
      (homSections ((PD.gradedMap r).app i) (u.op.obj V) ((PD.unit W).app i V x))
  rw [PD.gradedMap_unit, PD.gradedMap_unit, PD.gradedMap_unit]
  rfl

/-- The transport is additive. -/
theorem gradedMap_add
    (r r' : (forgetToGradedModule A').obj W ⟶ (forgetToGradedModule A').obj Z) :
    PD.gradedMap (r + r') = PD.gradedMap r + PD.gradedMap r' := by
  refine PD.graded_hom_ext fun i V x => ?_
  show homSections ((PD.gradedMap (r + r')).app i) (u.op.obj V) ((PD.unit W).app i V x) =
    homSections ((PD.gradedMap r).app i) (u.op.obj V) ((PD.unit W).app i V x) +
      homSections ((PD.gradedMap r').app i) (u.op.obj V) ((PD.unit W).app i V x)
  rw [PD.gradedMap_unit, PD.gradedMap_unit, PD.gradedMap_unit]
  exact map_add ((PD.unit Z).app i V) _ _

end PullbackData

end DifferentialGradedModule

end SheafOfModules

end

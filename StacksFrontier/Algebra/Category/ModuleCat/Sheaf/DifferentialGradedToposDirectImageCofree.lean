module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedConeIdentityShiftDown
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDirectImage

/-!
# The direct image of a cofree differential graded module

Let `f : X ⟶ Y` be a morphism of ringed topoi, presented as in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedToposDirectImage.lean` by an
additive lax monoidal functor `G` of sheaves of modules together with a unital homomorphism
`ψ : A ⟶ f_*B`, and write `f_{*,ψ}` for the direct image of right differential graded modules.
For a right differential graded `B`-module `Q`, **the direct image of the cofree differential
graded module on `Q[-1]` is the cofree differential graded module on `(f_{*,ψ}Q)[-1]`**:

`f_{*,ψ}(Cofree(Q[-1])) ≅ Cofree((f_{*,ψ}Q)[-1])`,

naturally in `Q`, where `Q[-1]` is
`SheafOfModules.DifferentialGradedModule.gradedShiftDown Q`.

This is the one thing the direct image of *differential* graded modules does not obviously carry:
a cofree module corepresents homomorphisms of *graded* modules, and the direct image is only
known degreewise. Both sides are `G(Q^{n-1}) ⊕ G(Q^n)` in degree `n`, the comparison is the
additivity of `G`, and the content is that the comparison respects the differential and the
twisted action.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.cofreeFst` is the first coordinate of a cofree module
  on a shift down by one, as a degree-lowering family of morphisms of sheaves of modules.
* `SheafOfModules.DifferentialGradedModule.toposCofreeFirst` is that coordinate pushed forward, as
  a homomorphism of graded modules out of `f_{*,ψ}(Cofree(Q[-1]))`.
* `SheafOfModules.DifferentialGradedModule.toposCofreeDesc` is the comparison morphism and
  `SheafOfModules.DifferentialGradedModule.toposCofreeIso` the isomorphism.

## Main results

* `SheafOfModules.DifferentialGradedModule.transport_map_mul_heq`: **an additive lax monoidal
  functor transports a right-linear degree-lowering family** between two different modules.
* `SheafOfModules.DifferentialGradedModule.isIso_toposCofreeDesc`: the comparison is an
  isomorphism, being in each degree the additivity comparison
  `G(M ⊞ N) ≅ G M ⊞ G N`.
* `SheafOfModules.DifferentialGradedModule.toposCofreeIso_naturality`: the comparison is natural
  in `Q`.

## Implementation notes

The comparison is **constructed out of the universal property of the target**, not degreewise: a
morphism into `Cofree(N)` is a homomorphism of graded modules into `N`, so it is enough to produce
one out of `f_{*,ψ}(Cofree(Q[-1]))` into `(f_{*,ψ}Q)[-1]`. The homomorphism is `G` applied to the
first coordinate `Cofree(Q[-1])^n = Q^{n-1} ⊕ Q^n ⟶ Q^{n-1}`, which is right `B`-linear because
the first coordinate of the cofree action is the unsigned one — the signed Leibniz term of the
cofree action sits in the *second* coordinate. That the transported family is right `A`-linear is
`transport_map_mul_heq` followed by the restriction of scalars along `ψ`.

Only then is the comparison computed degreewise, and there it is `biprod.lift (G fst) (G snd)`:
the second coordinate of a cofree lift is the first coordinate after the differential, and the
differential of a cofree module is `(x, y) ↦ (y, 0)`, so the two coordinates of the comparison are
`G` of the two projections. An additive functor inverts that, with
`biprod.desc (G inl) (G inr)`.

No sheafification of types, no smallness and no functor between the two underlying categories
appear: the hypotheses are those of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/DifferentialGradedToposDirectImage.lean`, with no
addition.

## References

* [Stacks Project, Tag 0FRU](https://stacks.math.columbia.edu/tag/0FRU)
* [Stacks Project, Tag 0FSK](https://stacks.math.columbia.edu/tag/0FSK)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CategoryTheory.Sheaf

universe w v₁ u₁ v₂ u₂

/-! ### A morphism into a binary biproduct which splits -/

namespace CategoryTheory.Limits

/-- **A morphism into a binary biproduct is an isomorphism when its two components split it.**
This is the dual of `CategoryTheory.Limits.biprod.isIso_desc`: given `a : Z ⟶ X` and `b : Z ⟶ Y`
together with `p : X ⟶ Z` and `q : Y ⟶ Z` which section `a` and `b` respectively and annihilate
the other one, and whose two products `a ≫ p` and `b ≫ q` add up to the identity of `Z`, the
morphism `biprod.lift a b` is an isomorphism, with inverse `biprod.desc p q`. -/
theorem biprod.isIso_lift {E : Type u₁} [Category.{v₁} E] [Preadditive E] {X Y Z : E}
    [HasBinaryBiproduct X Y] (a : Z ⟶ X) (b : Z ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    (hpa : p ≫ a = 𝟙 X) (hqa : q ≫ a = 0) (hpb : p ≫ b = 0) (hqb : q ≫ b = 𝟙 Y)
    (htotal : a ≫ p + b ≫ q = 𝟙 Z) : IsIso (biprod.lift a b) := by
  refine ⟨biprod.desc p q, ?_, ?_⟩
  · rw [biprod.lift_eq, Preadditive.add_comp, Category.assoc, Category.assoc,
      biprod.inl_desc, biprod.inr_desc]
    exact htotal
  · refine biprod.hom_ext' _ _ ?_ ?_ <;> refine biprod.hom_ext _ _ ?_ ?_ <;>
      simp [hpa, hqa, hpb, hqb]

/-- **An additive functor carries the two projections of a binary biproduct to the two
projections of one.** -/
theorem biprod.isIso_lift_map {E₁ : Type u₁} [Category.{v₁} E₁] [Preadditive E₁]
    {E₂ : Type u₂} [Category.{v₂} E₂] [Preadditive E₂] (L : E₁ ⥤ E₂) [L.Additive] (X Y : E₁)
    [HasBinaryBiproduct X Y] [HasBinaryBiproduct (L.obj X) (L.obj Y)] :
    IsIso (biprod.lift (L.map (biprod.fst : X ⊞ Y ⟶ X))
      (L.map (biprod.snd : X ⊞ Y ⟶ Y))) := by
  refine biprod.isIso_lift _ _ (L.map (biprod.inl : X ⟶ X ⊞ Y))
    (L.map (biprod.inr : Y ⟶ X ⊞ Y)) ?_ ?_ ?_ ?_ ?_
  · rw [← L.map_comp, biprod.inl_fst, L.map_id]
  · rw [← L.map_comp, biprod.inr_fst, L.map_zero]
  · rw [← L.map_comp, biprod.inl_snd, L.map_zero]
  · rw [← L.map_comp, biprod.inr_snd, L.map_id]
  · rw [← L.map_comp, ← L.map_comp, ← L.map_add, biprod.total, L.map_id]

end CategoryTheory.Limits

namespace SheafOfModules.DifferentialGradedModule

section Transport

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- **An additive lax monoidal functor transports a right-linear degree-lowering family.** This
is the `map_mul` half of `SheafOfModules.DifferentialGradedModule.transportHomotopy`, stated
between two different right differential graded modules: compatibility with the action is a
morphism-level identity once it is read through
`SheafOfModules.DifferentialGradedModule.smulSheaf_comp_heq_iff`, and a lax monoidal functor
transports such an identity by `Stacks.MonoidalGraded.mapMul_naturality`. -/
theorem transport_map_mul_heq
    (L : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
    [L.LaxMonoidal] [L.Additive] {E : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
    (X Y : DifferentialGradedModule.{w, w, w} E)
    (hO : Presheaf.IsSheaf J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
    (hP : Presheaf.IsSheaf K
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))
    (φ : ∀ n : ℤ, X.complex.X n ⟶ Y.complex.X (n - 1))
    (hφ : ∀ (n i : ℤ) (V : Cᵒᵖ) (ξ : (X.complex.X n).val.obj V)
        (b : (E.complex.X i).val.obj V),
      HEq ((φ (n + i)).val.app V ((X.mul n i).app V ξ b))
        ((Y.mul (n - 1) i).app V ((φ n).val.app V ξ) b))
    (n i : ℤ) (U : Dᵒᵖ)
    (x : ((transport L X hO hP).complex.X n).val.obj U)
    (y : ((DifferentialGradedAlgebra.transport L hO hP E).complex.X i).val.obj U) :
    HEq ((L.map (φ (n + i))).val.app U (((transport L X hO hP).mul n i).app U x y))
      (((transport L Y hO hP).mul (n - 1) i).app U ((L.map (φ n)).val.app U x) y) := by
  refine (smulSheaf_comp_heq_iff (transport L X hO hP) hP (transport L Y hO hP)
    (fun q ↦ L.map (φ q)) n i).mp ?_ U x y
  have hsrc : smulSheaf X n i ≫ φ (n + i) ≫
        eqToHom (congrArg Y.complex.X (show n + i - 1 = n - 1 + i by omega)) =
      (φ n ⊗ₘ 𝟙 (E.complex.X i)) ≫ smulSheaf Y (n - 1) i :=
    (smulSheaf_comp_heq_iff X hO Y φ n i).mpr fun V ξ b ↦ hφ n i V ξ b
  have hnat := Stacks.MonoidalGraded.mapMul_naturality L (smulSheaf X n i)
    (smulSheaf Y (n - 1) i) (φ n) (𝟙 (E.complex.X i))
    (φ (n + i) ≫ eqToHom (congrArg Y.complex.X (show n + i - 1 = n - 1 + i by omega)))
    hsrc
  rw [L.map_comp, L.map_id, eqToHom_map] at hnat
  rw [smulSheaf_transport, smulSheaf_transport]
  exact hnat

/-- **An additive lax monoidal functor transports a right-linear family of degree zero.** The
degree-zero companion of
`SheafOfModules.DifferentialGradedModule.transport_map_mul_heq`: a degreewise family which is not
assumed to commute with the differentials, only with the action. -/
theorem transport_map_mul
    (L : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
    [L.LaxMonoidal] [L.Additive] {E : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
    (X Y : DifferentialGradedModule.{w, w, w} E)
    (hO : Presheaf.IsSheaf J
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Osharp.obj))
    (hP : Presheaf.IsSheaf K
      (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf Psharp.obj))
    (φ : ∀ n : ℤ, X.complex.X n ⟶ Y.complex.X n)
    (hφ : ∀ (n i : ℤ) (V : Cᵒᵖ) (ξ : (X.complex.X n).val.obj V)
        (b : (E.complex.X i).val.obj V),
      (φ (n + i)).val.app V ((X.mul n i).app V ξ b) =
        (Y.mul n i).app V ((φ n).val.app V ξ) b)
    (n i : ℤ) (U : Dᵒᵖ)
    (x : ((transport L X hO hP).complex.X n).val.obj U)
    (y : ((DifferentialGradedAlgebra.transport L hO hP E).complex.X i).val.obj U) :
    (L.map (φ (n + i))).val.app U (((transport L X hO hP).mul n i).app U x y) =
      ((transport L Y hO hP).mul n i).app U ((L.map (φ n)).val.app U x) y := by
  refine (smulSheaf_comp_eq_iff (transport L X hO hP) hP (transport L Y hO hP)
    (fun q ↦ L.map (φ q)) n i).mp ?_ U x y
  have hsrc : smulSheaf X n i ≫ φ (n + i) =
      (φ n ⊗ₘ 𝟙 (E.complex.X i)) ≫ smulSheaf Y n i :=
    (smulSheaf_comp_eq_iff X hO Y φ n i).mpr fun V ξ b ↦ hφ n i V ξ b
  have hnat := Stacks.MonoidalGraded.mapMul_naturality L (smulSheaf X n i)
    (smulSheaf Y n i) (φ n) (𝟙 (E.complex.X i)) (φ (n + i)) hsrc
  rw [L.map_id] at hnat
  rw [smulSheaf_transport, smulSheaf_transport]
  exact hnat

end Transport

section DirectImage

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  [K.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Psharp : Sheaf K CommRingCat.{w}}
  [K.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify K AddCommGrpCat.{w}]

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

variable (G : SheafOfModules.{w} (toRingCat J Osharp) ⥤ SheafOfModules.{w} (toRingCat K Psharp))
  [G.LaxMonoidal] [G.Additive]
  {B : DifferentialGradedAlgebra.{w, w} (toRingCat J Osharp)}
  {A : DifferentialGradedAlgebra.{w, w} (toRingCat K Psharp)}

/-! ### The first coordinate of a cofree module on a shift down -/

section Coordinate

variable (Q : DifferentialGradedModule.{w, w, w} B)

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **The first coordinate of a cofree module is right linear.** The signed Leibniz term of the
cofree action sits in the *second* coordinate, so the first one carries the action across with no
sign; the transport identifies the two readings `(n + i) - 1` and `(n - 1) + i` of the degree the
shift stores a product in. -/
theorem cofreeFstHom_mul (n i : ℤ) (U : Cᵒᵖ)
    (ζ : ((Cofree.cofree (gradedShiftDown Q)).complex.X n).val.obj U)
    (b : (B.complex.X i).val.obj U) :
    HEq ((cofreeFstHom (gradedShiftDown Q) (n + i)).val.app U
        (((Cofree.cofree (gradedShiftDown Q)).mul n i).app U ζ b))
      ((Q.mul (n - 1) i).app U ((cofreeFstHom (gradedShiftDown Q) n).val.app U ζ) b) := by
  refine HEq.trans (heq_of_eq (Cofree.coordFst_mulHom (gradedShiftDown Q) n i U b ζ)) ?_
  exact gradedShiftDown_smul_eval_heq Q n i U _ b

end Coordinate

/-! ### The comparison -/

variable (ψ : A ⟶ toposPushforwardAlgebra G B) (hψ : ψ.IsUnital)

/-- Naturality of the comparisons of cofree modules, checked on first coordinates: `g` and `g'`
are the pushed-forward first coordinates, which `θ` and `θ'` have as first coordinates. -/
private theorem toposCofree_naturality {P P' : GradedModule.{w, w, w} B.toGradedAlgebra}
    {N N' : GradedModule.{w, w, w} A.toGradedAlgebra} (k : GradedModule.Hom P P')
    (k' : GradedModule.Hom N N')
    (θ : (toposPushforward G ψ hψ).obj (Cofree.cofree P) ⟶ Cofree.cofree N)
    (θ' : (toposPushforward G ψ hψ).obj (Cofree.cofree P') ⟶ Cofree.cofree N')
    (g : ∀ n, G.obj ((Cofree.cofree P).complex.X n) ⟶ N.piece n)
    (g' : ∀ n, G.obj ((Cofree.cofree P').complex.X n) ⟶ N'.piece n)
    (hθ : ∀ n, θ.toHomologicalComplex.f n ≫ cofreeFstHom N n = g n)
    (hθ' : ∀ n, θ'.toHomologicalComplex.f n ≫ cofreeFstHom N' n = g' n)
    (hg : ∀ n, G.map ((cofreeMap k).toHomologicalComplex.f n) ≫ g' n = g n ≫ k'.app n) :
    (toposPushforward G ψ hψ).map (cofreeMap k) ≫ θ' = θ ≫ cofreeMap k' := by
  refine lowerHom_injective _ (GradedModule.Hom.ext fun n => ?_)
  rw [lowerHom_app, lowerHom_app, comp_f, comp_f, Category.assoc, Category.assoc, hθ',
    cofreeMap_comp_fst, ← Category.assoc, hθ]
  exact hg n

/-- **The direct image of a right-linear degree-lowering family**, for the direct image of right
differential graded modules along a morphism of ringed topoi: `G` applied degreewise, with the
scalars of the two modules restricted along `ψ`. -/
theorem toposPushforward_map_mul_heq (X Y : DifferentialGradedModule.{w, w, w} B)
    (φ : ∀ n : ℤ, X.complex.X n ⟶ Y.complex.X (n - 1))
    (hφ : ∀ (n i : ℤ) (V : Cᵒᵖ) (ξ : (X.complex.X n).val.obj V)
        (b : (B.complex.X i).val.obj V),
      HEq ((φ (n + i)).val.app V ((X.mul n i).app V ξ b))
        ((Y.mul (n - 1) i).app V ((φ n).val.app V ξ) b))
    (n i : ℤ) (U : Dᵒᵖ)
    (x : (G.obj (X.complex.X n)).val.obj U) (y : (A.complex.X i).val.obj U) :
    HEq ((G.map (φ (n + i))).val.app U
        ((((toposPushforward G ψ hψ).obj X).mul n i).app U x y))
      ((((toposPushforward G ψ hψ).obj Y).mul (n - 1) i).app U
        ((G.map (φ n)).val.app U x) y) := by
  rw [toposPushforward_mul_app, toposPushforward_mul_app]
  exact transport_map_mul_heq G X Y _ _ φ hφ n i U x
    ((ψ.toHomologicalComplex.f i).val.app U y)

/-- **The first coordinate of a cofree module, pushed forward**: a homomorphism of graded modules
from the direct image of `Cofree(Q[-1])` into `(f_{*,ψ}Q)[-1]`. -/
noncomputable def toposCofreeFirst (Q : DifferentialGradedModule.{w, w, w} B) :
    GradedModule.Hom
      (GradedModule.ofDifferentialGraded
        ((toposPushforward G ψ hψ).obj (Cofree.cofree (gradedShiftDown Q))))
      (gradedShiftDown ((toposPushforward G ψ hψ).obj Q)) where
  app n := G.map (cofreeFstHom (gradedShiftDown Q) n)
  map_smul n i U x y := by
    refine eq_of_heq (HEq.trans ?_ (gradedShiftDown_smul_eval_heq
      ((toposPushforward G ψ hψ).obj Q) n i U _ y).symm)
    exact toposPushforward_map_mul_heq G ψ hψ (Cofree.cofree (gradedShiftDown Q)) Q
      (cofreeFstHom (gradedShiftDown Q)) (cofreeFstHom_mul Q) n i U x y

/-- The degree-`n` component of `toposCofreeFirst` is `G` of the degree-`n` first coordinate. -/
@[simp] theorem toposCofreeFirst_app (Q : DifferentialGradedModule.{w, w, w} B) (n : ℤ) :
    (toposCofreeFirst G ψ hψ Q).app n = G.map (cofreeFstHom (gradedShiftDown Q) n) := rfl

/-- **The comparison morphism** `f_{*,ψ}(Cofree(Q[-1])) ⟶ Cofree((f_{*,ψ}Q)[-1])`: the cofree
lift of the pushed-forward first coordinate. -/
noncomputable def toposCofreeDesc (Q : DifferentialGradedModule.{w, w, w} B) :
    (toposPushforward G ψ hψ).obj (Cofree.cofree (gradedShiftDown Q)) ⟶
      Cofree.cofree (gradedShiftDown ((toposPushforward G ψ hψ).obj Q)) :=
  Cofree.liftDgHom _ (toposCofreeFirst G ψ hψ Q)

/-- **The first coordinate of the comparison is the pushed-forward first coordinate.** -/
theorem toposCofreeDesc_comp_fst (Q : DifferentialGradedModule.{w, w, w} B) (n : ℤ) :
    (toposCofreeDesc G ψ hψ Q).toHomologicalComplex.f n ≫
        cofreeFstHom (gradedShiftDown ((toposPushforward G ψ hψ).obj Q)) n =
      G.map (cofreeFstHom (gradedShiftDown Q) n) :=
  liftHom_comp_fstHom (toposCofreeFirst G ψ hψ Q) n

/-- **The comparison in degree `n` is the additivity comparison of `G`**: its first coordinate is
`G` applied to the first projection and its second is `G` applied to the second, the second
coordinate of a cofree lift being the first coordinate after the differential. -/
theorem toposCofreeDesc_f (Q : DifferentialGradedModule.{w, w, w} B) (n : ℤ) :
    (toposCofreeDesc G ψ hψ Q).toHomologicalComplex.f n =
      biprod.lift (G.map (cofreeFstHom (gradedShiftDown Q) n))
        (G.map (cofreeSndHom (gradedShiftDown Q) n)) := by
  change biprod.lift (G.map (cofreeFstHom (gradedShiftDown Q) n))
    (G.map ((Cofree.cofree (gradedShiftDown Q)).complex.d n (n + 1)) ≫
      G.map (cofreeFstHom (gradedShiftDown Q) (n + 1))) = _
  rw [← G.map_comp, cofree_d_comp_fstHom]

/-- **The comparison is an isomorphism.** In degree `n` it is
`biprod.lift (G fst) (G snd) : G(M ⊞ N) ⟶ G M ⊞ G N`, which an additive functor inverts. -/
theorem isIso_toposCofreeDesc (Q : DifferentialGradedModule.{w, w, w} B) :
    IsIso (toposCofreeDesc G ψ hψ Q) :=
  isIso_of_componentwise _ fun n => by
    rw [toposCofreeDesc_f]
    exact biprod.isIso_lift_map G ((gradedShiftDown Q).piece n)
      ((gradedShiftDown Q).piece (n + 1))

/-- **The direct image of the cofree module on `Q[-1]` is the cofree module on
`(f_{*,ψ}Q)[-1]`.** -/
noncomputable def toposCofreeIso (Q : DifferentialGradedModule.{w, w, w} B) :
    (toposPushforward G ψ hψ).obj (Cofree.cofree (gradedShiftDown Q)) ≅
      Cofree.cofree (gradedShiftDown ((toposPushforward G ψ hψ).obj Q)) :=
  haveI := isIso_toposCofreeDesc G ψ hψ Q
  asIso (toposCofreeDesc G ψ hψ Q)

/-- The forward map of `toposCofreeIso` is `toposCofreeDesc`. -/
@[simp] theorem toposCofreeIso_hom (Q : DifferentialGradedModule.{w, w, w} B) :
    (toposCofreeIso G ψ hψ Q).hom = toposCofreeDesc G ψ hψ Q := rfl

/-- **The comparison is natural in `Q`.** Both sides are morphisms into a cofree module, so the
identity is checked on the first coordinate, where each side is `G` of the first coordinate
followed by `G` of the degree-`n - 1` component of the given morphism. -/
theorem toposCofreeDesc_naturality {Q Q' : DifferentialGradedModule.{w, w, w} B} (g : Q ⟶ Q') :
    (toposPushforward G ψ hψ).map (cofreeMap (gradedShiftDownMap g)) ≫
        toposCofreeDesc G ψ hψ Q' =
      toposCofreeDesc G ψ hψ Q ≫
        cofreeMap (gradedShiftDownMap ((toposPushforward G ψ hψ).map g)) :=
  toposCofree_naturality G ψ hψ _ _ _ _ _ _ (toposCofreeDesc_comp_fst G ψ hψ Q)
    (toposCofreeDesc_comp_fst G ψ hψ Q') fun n =>
    (G.map_comp _ _).symm.trans
      ((congrArg G.map (cofreeMap_comp_fst _ n)).trans (G.map_comp _ _))

/-- **The comparison is compatible with the two counits**: `θ` followed by the counit of
`(f_{*,ψ}Q)[-1]` is the direct image of the counit of `Q[-1]`. In degree `n` both sides are
`G(fst) ≫ G(d) + G(snd)`, the one because `G` is additive and the other because the comparison is
`biprod.lift (G fst) (G snd)`. -/
theorem toposCofreeDesc_comp_counit (Q : DifferentialGradedModule.{w, w, w} B) :
    toposCofreeDesc G ψ hψ Q ≫ cofreeCounit ((toposPushforward G ψ hψ).obj Q) =
      (toposPushforward G ψ hψ).map (cofreeCounit Q) := by
  refine Hom.ext fun n => ?_
  change (toposCofreeDesc G ψ hψ Q).toHomologicalComplex.f n ≫
      (cofreeCounit ((toposPushforward G ψ hψ).obj Q)).toHomologicalComplex.f n =
    G.map ((cofreeCounit Q).toHomologicalComplex.f n)
  rw [toposCofreeDesc_f, cofreeCounit_f]
  refine Eq.trans (lift_comp_coords _ n _ _ _ _) ?_
  rw [cofreeCounit_f, G.map_add]
  refine congrArg₂ (· + ·) (G.map_comp _ _).symm ?_
  exact (Eq.trans (G.map_comp _ _)
    (congrArg (fun z => G.map (cofreeSndHom (gradedShiftDown Q) n) ≫ z)
      (eqToHom_map G (congrArg Q.complex.X (degSuccSubOne n))))).symm

/-! ### The direct image of a cofree module on an unshifted underlying graded module -/

section Unshifted

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- **The first coordinate of a cofree module on the underlying graded module is right
linear**, the degree-zero companion of
`SheafOfModules.DifferentialGradedModule.cofreeFstHom_mul`. The signed Leibniz term of the cofree
action sits in the second coordinate, so no sign and no transport appears. -/
theorem cofreeFstHom_mul_graded (Q : DifferentialGradedModule.{w, w, w} B) (n i : ℤ) (U : Cᵒᵖ)
    (ζ : ((Cofree.cofree (GradedModule.ofDifferentialGraded Q)).complex.X n).val.obj U)
    (b : (B.complex.X i).val.obj U) :
    (cofreeFstHom (GradedModule.ofDifferentialGraded Q) (n + i)).val.app U
        (((Cofree.cofree (GradedModule.ofDifferentialGraded Q)).mul n i).app U ζ b) =
      (Q.mul n i).app U
        ((cofreeFstHom (GradedModule.ofDifferentialGraded Q) n).val.app U ζ) b :=
  Cofree.coordFst_mulHom (GradedModule.ofDifferentialGraded Q) n i U b ζ

/-- **The direct image of a right-linear family of degree zero**, for the direct image of right
differential graded modules along a morphism of ringed topoi. -/
theorem toposPushforward_map_mul (X Y : DifferentialGradedModule.{w, w, w} B)
    (φ : ∀ n : ℤ, X.complex.X n ⟶ Y.complex.X n)
    (hφ : ∀ (n i : ℤ) (V : Cᵒᵖ) (ξ : (X.complex.X n).val.obj V)
        (b : (B.complex.X i).val.obj V),
      (φ (n + i)).val.app V ((X.mul n i).app V ξ b) =
        (Y.mul n i).app V ((φ n).val.app V ξ) b)
    (n i : ℤ) (U : Dᵒᵖ)
    (x : (G.obj (X.complex.X n)).val.obj U) (y : (A.complex.X i).val.obj U) :
    (G.map (φ (n + i))).val.app U
        ((((toposPushforward G ψ hψ).obj X).mul n i).app U x y) =
      (((toposPushforward G ψ hψ).obj Y).mul n i).app U
        ((G.map (φ n)).val.app U x) y := by
  rw [toposPushforward_mul_app, toposPushforward_mul_app]
  exact transport_map_mul G X Y _ _ φ hφ n i U x
    ((ψ.toHomologicalComplex.f i).val.app U y)

/-- **The first coordinate of a cofree module on an underlying graded module, pushed forward.** -/
noncomputable def toposCofreeFirstGraded (Q : DifferentialGradedModule.{w, w, w} B) :
    GradedModule.Hom
      (GradedModule.ofDifferentialGraded
        ((toposPushforward G ψ hψ).obj (Cofree.cofree (GradedModule.ofDifferentialGraded Q))))
      (GradedModule.ofDifferentialGraded ((toposPushforward G ψ hψ).obj Q)) where
  app n := G.map (cofreeFstHom (GradedModule.ofDifferentialGraded Q) n)
  map_smul n i U x y :=
    toposPushforward_map_mul G ψ hψ (Cofree.cofree (GradedModule.ofDifferentialGraded Q)) Q
      (cofreeFstHom (GradedModule.ofDifferentialGraded Q)) (cofreeFstHom_mul_graded Q) n i U x y

/-- **The comparison** `f_{*,ψ}(Cofree(gr Q)) ⟶ Cofree(gr (f_{*,ψ}Q))`. -/
noncomputable def toposCofreeDescGraded (Q : DifferentialGradedModule.{w, w, w} B) :
    (toposPushforward G ψ hψ).obj (Cofree.cofree (GradedModule.ofDifferentialGraded Q)) ⟶
      Cofree.cofree
        (GradedModule.ofDifferentialGraded ((toposPushforward G ψ hψ).obj Q)) :=
  Cofree.liftDgHom _ (toposCofreeFirstGraded G ψ hψ Q)

/-- **The first coordinate of the comparison.** -/
theorem toposCofreeDescGraded_comp_fst (Q : DifferentialGradedModule.{w, w, w} B) (n : ℤ) :
    (toposCofreeDescGraded G ψ hψ Q).toHomologicalComplex.f n ≫
        cofreeFstHom
          (GradedModule.ofDifferentialGraded ((toposPushforward G ψ hψ).obj Q)) n =
      G.map (cofreeFstHom (GradedModule.ofDifferentialGraded Q) n) :=
  liftHom_comp_fstHom (toposCofreeFirstGraded G ψ hψ Q) n

/-- **The comparison in degree `n` is the additivity comparison of `G`.** -/
theorem toposCofreeDescGraded_f (Q : DifferentialGradedModule.{w, w, w} B) (n : ℤ) :
    (toposCofreeDescGraded G ψ hψ Q).toHomologicalComplex.f n =
      biprod.lift (G.map (cofreeFstHom (GradedModule.ofDifferentialGraded Q) n))
        (G.map (cofreeSndHom (GradedModule.ofDifferentialGraded Q) n)) := by
  change biprod.lift (G.map (cofreeFstHom (GradedModule.ofDifferentialGraded Q) n))
    (G.map ((Cofree.cofree (GradedModule.ofDifferentialGraded Q)).complex.d n (n + 1)) ≫
      G.map (cofreeFstHom (GradedModule.ofDifferentialGraded Q) (n + 1))) = _
  rw [← G.map_comp, cofree_d_comp_fstHom]

/-- **The comparison is an isomorphism.** -/
theorem isIso_toposCofreeDescGraded (Q : DifferentialGradedModule.{w, w, w} B) :
    IsIso (toposCofreeDescGraded G ψ hψ Q) :=
  isIso_of_componentwise _ fun n => by
    rw [toposCofreeDescGraded_f]
    exact biprod.isIso_lift_map G ((GradedModule.ofDifferentialGraded Q).piece n)
      ((GradedModule.ofDifferentialGraded Q).piece (n + 1))

/-- **The direct image of the cofree module on `gr Q` is the cofree module on
`gr (f_{*,ψ}Q)`.** -/
noncomputable def toposCofreeIsoGraded (Q : DifferentialGradedModule.{w, w, w} B) :
    (toposPushforward G ψ hψ).obj (Cofree.cofree (GradedModule.ofDifferentialGraded Q)) ≅
      Cofree.cofree
        (GradedModule.ofDifferentialGraded ((toposPushforward G ψ hψ).obj Q)) :=
  haveI := isIso_toposCofreeDescGraded G ψ hψ Q
  asIso (toposCofreeDescGraded G ψ hψ Q)

/-- The forward map of `toposCofreeIsoGraded` is `toposCofreeDescGraded`. -/
@[simp] theorem toposCofreeIsoGraded_hom (Q : DifferentialGradedModule.{w, w, w} B) :
    (toposCofreeIsoGraded G ψ hψ Q).hom = toposCofreeDescGraded G ψ hψ Q := rfl

/-- **The comparison is natural in `Q`.** -/
theorem toposCofreeDescGraded_naturality
    {Q Q' : DifferentialGradedModule.{w, w, w} B} (g : Q ⟶ Q') :
    (toposPushforward G ψ hψ).map
          (cofreeMap (GradedModule.ofDifferentialGradedMap g)) ≫
        toposCofreeDescGraded G ψ hψ Q' =
      toposCofreeDescGraded G ψ hψ Q ≫
        cofreeMap (GradedModule.ofDifferentialGradedMap
          ((toposPushforward G ψ hψ).map g)) :=
  toposCofree_naturality G ψ hψ _ _ _ _ _ _ (toposCofreeDescGraded_comp_fst G ψ hψ Q)
    (toposCofreeDescGraded_comp_fst G ψ hψ Q') fun n =>
    (G.map_comp _ _).symm.trans
      ((congrArg G.map (cofreeMap_comp_fst _ n)).trans (G.map_comp _ _))

/-! ### The direct image of a homomorphism of underlying graded modules -/

/-- **The direct image of a homomorphism of underlying graded modules**: `G` applied degreewise,
with the scalars of the two modules restricted along `ψ`. -/
noncomputable def toposGradedPushMap {X Y : DifferentialGradedModule.{w, w, w} B}
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded X)
      (GradedModule.ofDifferentialGraded Y)) :
    GradedModule.Hom
      (GradedModule.ofDifferentialGraded ((toposPushforward G ψ hψ).obj X))
      (GradedModule.ofDifferentialGraded ((toposPushforward G ψ hψ).obj Y)) where
  app n := G.map (Φ.app n)
  map_smul n i U x y :=
    toposPushforward_map_mul G ψ hψ X Y (fun q => Φ.app q) Φ.map_smul n i U x y

/-- The degree-`n` component of `toposGradedPushMap G ψ hψ Φ` is `G` of the degree-`n` component
of `Φ`. -/
@[simp] theorem toposGradedPushMap_app {X Y : DifferentialGradedModule.{w, w, w} B}
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded X)
      (GradedModule.ofDifferentialGraded Y)) (n : ℤ) :
    (toposGradedPushMap G ψ hψ Φ).app n = G.map (Φ.app n) := rfl

/-- The direct image of the identity is the identity. -/
theorem toposGradedPushMap_id (X : DifferentialGradedModule.{w, w, w} B) :
    toposGradedPushMap G ψ hψ (𝟙 (GradedModule.ofDifferentialGraded X)) =
      𝟙 (GradedModule.ofDifferentialGraded ((toposPushforward G ψ hψ).obj X)) :=
  GradedModule.Hom.ext fun n => by
    change G.map (𝟙 (X.complex.X n)) = 𝟙 _
    rw [G.map_id]

/-- The direct image of a composite is the composite of the direct images. -/
theorem toposGradedPushMap_comp {X Y Z : DifferentialGradedModule.{w, w, w} B}
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded X)
      (GradedModule.ofDifferentialGraded Y))
    (Φ' : GradedModule.Hom (GradedModule.ofDifferentialGraded Y)
      (GradedModule.ofDifferentialGraded Z)) :
    toposGradedPushMap G ψ hψ (Φ.comp Φ') =
      (toposGradedPushMap G ψ hψ Φ).comp (toposGradedPushMap G ψ hψ Φ') :=
  GradedModule.Hom.ext fun n => by
    change G.map (Φ.app n ≫ Φ'.app n) = G.map (Φ.app n) ≫ G.map (Φ'.app n)
    rw [G.map_comp]

/-- The direct image of the underlying homomorphism of a morphism of right differential graded
modules is the underlying homomorphism of its direct image. -/
theorem toposGradedPushMap_ofDifferentialGradedMap
    {X Y : DifferentialGradedModule.{w, w, w} B} (h : X ⟶ Y) :
    toposGradedPushMap G ψ hψ (GradedModule.ofDifferentialGradedMap h) =
      GradedModule.ofDifferentialGradedMap ((toposPushforward G ψ hψ).map h) :=
  GradedModule.Hom.ext fun _ => rfl

/-- **The unit of the cofree adjunction**, as a morphism of right differential graded modules
`Q ⟶ Cofree(gr Q)`. -/
noncomputable def cofreeUnitGraded (Q : DifferentialGradedModule.{w, w, w} B) :
    Q ⟶ Cofree.cofree (GradedModule.ofDifferentialGraded Q) :=
  Cofree.liftDgHom _ (𝟙 (GradedModule.ofDifferentialGraded Q))

omit [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}] in
/-- The unit `Q ⟶ Cofree(gr Q)` followed by the first coordinate is the identity in each degree. -/
theorem cofreeUnitGraded_comp_fst (Q : DifferentialGradedModule.{w, w, w} B) (n : ℤ) :
    (cofreeUnitGraded Q).toHomologicalComplex.f n ≫
        cofreeFstHom (GradedModule.ofDifferentialGraded Q) n = 𝟙 _ :=
  liftHom_comp_fstHom (𝟙 (GradedModule.ofDifferentialGraded Q)) n

/-- **The comparison carries the unit of the cofree adjunction to the unit.** -/
theorem toposPushforward_cofreeUnitGraded (Q : DifferentialGradedModule.{w, w, w} B) :
    (toposPushforward G ψ hψ).map (cofreeUnitGraded Q) ≫ toposCofreeDescGraded G ψ hψ Q =
      cofreeUnitGraded ((toposPushforward G ψ hψ).obj Q) := by
  refine lowerHom_injective _ (GradedModule.Hom.ext fun n => ?_)
  rw [lowerHom_app, comp_f, Category.assoc, toposCofreeDescGraded_comp_fst]
  change G.map ((cofreeUnitGraded Q).toHomologicalComplex.f n) ≫
      G.map (cofreeFstHom (GradedModule.ofDifferentialGraded Q) n) =
    (Cofree.lowerHom _ (cofreeUnitGraded ((toposPushforward G ψ hψ).obj Q))).app n
  rw [← G.map_comp, cofreeUnitGraded_comp_fst, lowerHom_app, cofreeUnitGraded_comp_fst]
  exact G.map_id _

/-- **The first coordinate of the direct image of a cofree lift is the direct image of the
graded homomorphism.** This is the formula which turns the base change of a graded homomorphism
into the direct image of that homomorphism precomposed with the unit. -/
theorem lowerHom_map_liftDgHom {X : DifferentialGradedModule.{w, w, w} B}
    (Q : DifferentialGradedModule.{w, w, w} B)
    (Φ : GradedModule.Hom (GradedModule.ofDifferentialGraded X)
      (GradedModule.ofDifferentialGraded Q)) :
    Cofree.lowerHom _
        ((toposPushforward G ψ hψ).map
            (Cofree.liftDgHom (GradedModule.ofDifferentialGraded Q) Φ) ≫
          toposCofreeDescGraded G ψ hψ Q) =
      toposGradedPushMap G ψ hψ Φ := by
  refine GradedModule.Hom.ext fun n => ?_
  rw [lowerHom_app, comp_f, Category.assoc, toposCofreeDescGraded_comp_fst]
  change G.map ((Cofree.liftDgHom (GradedModule.ofDifferentialGraded Q) Φ).toHomologicalComplex.f n)
      ≫ G.map (cofreeFstHom (GradedModule.ofDifferentialGraded Q) n) = G.map (Φ.app n)
  rw [← G.map_comp]
  exact congrArg G.map (liftHom_comp_fstHom Φ n)

end Unshifted

end DirectImage

end SheafOfModules.DifferentialGradedModule

end

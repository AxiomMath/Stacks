module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.QuotientRestriction

/-!
# The algebraization comparison map as a map of `A`-modules

Let `I ⊆ 𝔞` be ideals of a Noetherian ring `A`, let `U = Spec(A) ∖ V(𝔞)` and let `ℱ` be a module
on `U`. The comparison map `Stacks.Algebraization.comparisonMap`

`colim_V Γ(V, ℱ) ⟶ lim_n Γ(U, ℱ / Iⁿ ℱ)`,

the colimit being over the opens `V ⊆ U` containing `U ∩ V(I)`, is a map of abelian groups. Every
`Γ(V, ℱ)` is a module over `Γ(V, 𝒪_U)`, hence over `A` through the ring map
`A ⟶ Γ(U, 𝒪_U) ⟶ Γ(V, 𝒪_U)` coming from the open immersion `U ⟶ Spec(A)`, and multiplication by
a fixed `r : A` is a natural endomorphism of each of the two diagrams. The induced endomorphisms
of the colimit and of the limit make each side an object of `ModuleCat A`, and the comparison map
is linear for them.

## Main definitions

* `Stacks.Algebraization.complementBaseScalars` and `Stacks.Algebraization.opensScalars` — the
  ring maps `A ⟶ Γ(U, 𝒪_U)` and `A ⟶ Γ(V, 𝒪_U)`.
* `Stacks.Algebraization.smulPresheaf` — multiplication by `r : A` on the presheaf of sections
  of a module on `U`.
* `Stacks.Algebraization.smulSectionsNearVanishing` and
  `Stacks.Algebraization.smulFormalSections` — multiplication by `r : A` on the two diagrams.
* `Stacks.Algebraization.colimSectionsSmul` and
  `Stacks.Algebraization.limFormalSectionsSmul` — the two ring maps from `A` to the
  endomorphisms of the colimit and of the limit.
* `Stacks.Algebraization.sectionsNearVanishingColimit` and
  `Stacks.Algebraization.formalSectionsLimit` — the two sides of the comparison map, as
  `A`-modules.
* `Stacks.Algebraization.comparisonModuleMap` — the comparison map as a map of `A`-modules.

## Main results

* `Stacks.Algebraization.comparisonMap_comp_smul` — the comparison map is `A`-linear.
* `Stacks.Algebraization.forget₂_comparisonModuleMap` — the underlying map of abelian groups of
  the `A`-linear comparison map is `Stacks.Algebraization.comparisonMap`.
* `Stacks.Algebraization.isIso_comparisonModuleMap_iff` — the `A`-linear comparison map is an
  isomorphism exactly when the comparison map is.

## References

* [Stacks Project, Tag 0EG2](https://stacks.math.columbia.edu/tag/0EG2)
* [Stacks Project, Tag 0DXR](https://stacks.math.columbia.edu/tag/0DXR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.Algebraization

open Stacks.LocalCohomology

/-! ### Functoriality and additivity of the maps induced on a colimit and on a limit -/

section Induced

variable {J : Type*} [Category J] {C : Type*} [Category C] [Preadditive C] {D : J ⥤ C}

omit [Preadditive C] in
/-- The map induced on the colimit by the identity is the identity. -/
private theorem colimMap_id [HasColimit D] : colimMap (𝟙 D) = 𝟙 (colimit D) := by
  refine colimit.hom_ext fun j ↦ ?_
  rw [ι_colimMap, NatTrans.id_app, Category.id_comp, Category.comp_id]

omit [Preadditive C] in
/-- The map induced on the colimit by a composite is the composite of the induced maps. -/
private theorem colimMap_comp' [HasColimit D] (α β : D ⟶ D) :
    colimMap (α ≫ β) = colimMap α ≫ colimMap β := by
  refine colimit.hom_ext fun j ↦ ?_
  rw [ι_colimMap, NatTrans.comp_app, ι_colimMap_assoc, ι_colimMap, Category.assoc]

/-- The map induced on the colimit by the zero morphism of diagrams is zero. -/
private theorem colimMap_zero [HasColimit D] : colimMap (0 : D ⟶ D) = 0 := by
  refine colimit.hom_ext fun j ↦ ?_
  rw [ι_colimMap, NatTrans.app_zero, Limits.zero_comp, Limits.comp_zero]

/-- The map induced on the colimit is additive in the morphism of diagrams. -/
private theorem colimMap_add [HasColimit D] (α β : D ⟶ D) :
    colimMap (α + β) = colimMap α + colimMap β := by
  refine colimit.hom_ext fun j ↦ ?_
  rw [ι_colimMap, NatTrans.app_add, Preadditive.add_comp, Preadditive.comp_add, ι_colimMap,
    ι_colimMap]

omit [Preadditive C] in
/-- The map induced on the limit by the identity is the identity. -/
private theorem limMap_id [HasLimit D] : limMap (𝟙 D) = 𝟙 (limit D) := by
  refine limit.hom_ext fun j ↦ ?_
  rw [limMap_π, NatTrans.id_app, Category.comp_id, Category.id_comp]

omit [Preadditive C] in
/-- The map induced on the limit by a composite is the composite of the induced maps. -/
private theorem limMap_comp' [HasLimit D] (α β : D ⟶ D) :
    limMap (α ≫ β) = limMap α ≫ limMap β := by
  refine limit.hom_ext fun j ↦ ?_
  rw [limMap_π, NatTrans.comp_app, Category.assoc, limMap_π, limMap_π_assoc]

/-- The map induced on the limit by the zero morphism of diagrams is zero. -/
private theorem limMap_zero [HasLimit D] : limMap (0 : D ⟶ D) = 0 := by
  refine limit.hom_ext fun j ↦ ?_
  rw [limMap_π, NatTrans.app_zero, Limits.comp_zero, Limits.zero_comp]

/-- The map induced on the limit is additive in the morphism of diagrams. -/
private theorem limMap_add [HasLimit D] (α β : D ⟶ D) :
    limMap (α + β) = limMap α + limMap β := by
  refine limit.hom_ext fun j ↦ ?_
  rw [limMap_π, NatTrans.app_add, Preadditive.comp_add, Preadditive.add_comp, limMap_π, limMap_π]

end Induced

/-! ### Scalars on the sections of a module on the complement of a zero locus -/

section Scalars

variable (A : Type u) [CommRing A] (a : Ideal A)

/-- The ring map `A ⟶ Γ(U, 𝒪_U)` for `U = Spec(A) ∖ V(𝔞)`, induced by the open immersion. -/
public def complementBaseScalars : A →+* Γ((complementZeroLocus A a : Scheme), ⊤) :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫ (complementZeroLocus A a).ι.appTop).hom

/-- The ring map `A ⟶ Γ(V, 𝒪_U)` on an open `V` of `U = Spec(A) ∖ V(𝔞)`: the global scalars
restricted to `V`. -/
public def opensScalars (V : (complementZeroLocus A a : Scheme).Opens) :
    A →+* Γ((complementZeroLocus A a : Scheme), V) :=
  (((complementZeroLocus A a : Scheme).presheaf.map (homOfLE (le_top (a := V))).op).hom).comp
    (complementBaseScalars A a)

/-- The scalars of `A` on the opens of `U` are compatible with restriction. -/
public theorem opensScalars_res {V W : (complementZeroLocus A a : Scheme).Opens} (i : W ⟶ V)
    (r : A) :
    ((complementZeroLocus A a : Scheme).presheaf.map i.op).hom (opensScalars A a V r) =
      opensScalars A a W r := by
  change ((complementZeroLocus A a : Scheme).presheaf.map (homOfLE (le_top (a := V))).op ≫
      (complementZeroLocus A a : Scheme).presheaf.map i.op).hom (complementBaseScalars A a r) = _
  rw [← (complementZeroLocus A a : Scheme).presheaf.map_comp]
  rfl

/-- Morphisms of modules commute with scalar multiplication on sections. -/
public theorem app_comp_smul {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N) {V : X.Opens}
    (r : Γ(X, V)) :
    φ.app V ≫ (N.smul r).asHom = (M.smul r).asHom ≫ φ.app V :=
  ModuleCat.smul_naturality (φ.val.app (op V)) r

/-- Multiplication by `r : A` on the sections of a module on `U`, as an endomorphism of the
underlying presheaf of abelian groups. -/
public def smulPresheaf (G : (complementZeroLocus A a : Scheme).Modules) (r : A) :
    G.presheaf ⟶ G.presheaf where
  app V := (G.smul (opensScalars A a V.unop r)).asHom
  naturality V W i := by
    have h := Scheme.Modules.map_comp_smul (M := G) i.unop (opensScalars A a V.unop r)
    rw [opensScalars_res] at h
    exact h.symm

end Scalars

/-! ### Multiplication by `A` on the two sides of the comparison map -/

variable (A : Type u) [CommRing A] (I a : Ideal A)
  (F : (complementZeroLocus A a : Scheme).Modules)

/-- Multiplication by `r : A` on the diagram of sections near the formal locus. -/
public def smulSectionsNearVanishing (r : A) :
    sectionsNearVanishing A I a F ⟶ sectionsNearVanishing A I a F :=
  Functor.whiskerLeft (opensNearVanishingFunctor A I a) (smulPresheaf A a F r)

/-- On a neighbourhood `V` of the formal locus, multiplication by `r` is multiplication by the
image of `r` in `Γ(V, 𝒪_U)`. -/
public theorem smulSectionsNearVanishing_app (r : A) (V : OpensNearVanishing A I a) :
    (smulSectionsNearVanishing A I a F r).app V = (F.smul (opensScalars A a V.openSet r)).asHom :=
  rfl

/-- Multiplication by `1` on the sections near the formal locus is the identity. -/
public theorem smulSectionsNearVanishing_one :
    smulSectionsNearVanishing A I a F 1 = 𝟙 (sectionsNearVanishing A I a F) :=
  NatTrans.ext (funext fun V ↦ by simp [smulSectionsNearVanishing_app]; rfl)

/-- Multiplication by a product on the sections near the formal locus is the composite. -/
public theorem smulSectionsNearVanishing_mul (r s : A) :
    smulSectionsNearVanishing A I a F (r * s) =
      smulSectionsNearVanishing A I a F s ≫ smulSectionsNearVanishing A I a F r :=
  NatTrans.ext (funext fun V ↦ by simp [smulSectionsNearVanishing_app]; rfl)

/-- Multiplication by `0` on the sections near the formal locus is zero. -/
public theorem smulSectionsNearVanishing_zero :
    smulSectionsNearVanishing A I a F 0 = 0 :=
  NatTrans.ext (funext fun V ↦ by simp [smulSectionsNearVanishing_app]; rfl)

/-- Multiplication on the sections near the formal locus is additive in the scalar. -/
public theorem smulSectionsNearVanishing_add (r s : A) :
    smulSectionsNearVanishing A I a F (r + s) =
      smulSectionsNearVanishing A I a F r + smulSectionsNearVanishing A I a F s :=
  NatTrans.ext (funext fun V ↦ by simp [smulSectionsNearVanishing_app]; rfl)

/-- Multiplication by `r : A` on the inverse system of formal sections. -/
public def smulFormalSections (r : A) : formalSections A I a F ⟶ formalSections A I a F where
  app n := (((quotientSystemNearVanishing A I a F).obj n).smul (opensScalars A a ⊤ r)).asHom
  naturality _ _ h :=
    app_comp_smul ((quotientSystemNearVanishing A I a F).map h) (opensScalars A a ⊤ r)

/-- In degree `n`, multiplication by `r` on the formal sections is multiplication by the image
of `r` in `Γ(U, 𝒪_U)` on the sections of `ℱ / Iⁿ ℱ`. -/
public theorem smulFormalSections_app (r : A) (n : ℕᵒᵖ) :
    (smulFormalSections A I a F r).app n =
      (((quotientSystemNearVanishing A I a F).obj n).smul (opensScalars A a ⊤ r)).asHom :=
  rfl

/-- Multiplication by `1` on the formal sections is the identity. -/
public theorem smulFormalSections_one :
    smulFormalSections A I a F 1 = 𝟙 (formalSections A I a F) :=
  NatTrans.ext (funext fun n ↦ by simp [smulFormalSections_app]; rfl)

/-- Multiplication by a product on the formal sections is the composite. -/
public theorem smulFormalSections_mul (r s : A) :
    smulFormalSections A I a F (r * s) =
      smulFormalSections A I a F s ≫ smulFormalSections A I a F r :=
  NatTrans.ext (funext fun n ↦ by simp [smulFormalSections_app]; rfl)

/-- Multiplication by `0` on the formal sections is zero. -/
public theorem smulFormalSections_zero : smulFormalSections A I a F 0 = 0 :=
  NatTrans.ext (funext fun n ↦ by simp [smulFormalSections_app]; rfl)

/-- Multiplication on the formal sections is additive in the scalar. -/
public theorem smulFormalSections_add (r s : A) :
    smulFormalSections A I a F (r + s) =
      smulFormalSections A I a F r + smulFormalSections A I a F s :=
  NatTrans.ext (funext fun n ↦ by simp [smulFormalSections_app]; rfl)

/-- Multiplication by `A` on the colimit of the sections near the formal locus. -/
public def colimSectionsSmul : A →+* End (colimit (sectionsNearVanishing A I a F)) where
  toFun r := End.of (colimMap (smulSectionsNearVanishing A I a F r))
  map_one' := by rw [smulSectionsNearVanishing_one, colimMap_id]; rfl
  map_mul' r s := by rw [smulSectionsNearVanishing_mul, colimMap_comp']; rfl
  map_zero' := by rw [smulSectionsNearVanishing_zero, colimMap_zero]; rfl
  map_add' r s := by rw [smulSectionsNearVanishing_add, colimMap_add]; rfl

/-- Multiplication by `r` on the colimit is the map induced by multiplication by `r` on the
diagram of sections. -/
public theorem colimSectionsSmul_apply (r : A) :
    (colimSectionsSmul A I a F r).asHom = colimMap (smulSectionsNearVanishing A I a F r) :=
  rfl

/-- Multiplication by `A` on the limit of the formal sections. -/
public def limFormalSectionsSmul : A →+* End (limit (formalSections A I a F)) where
  toFun r := End.of (limMap (smulFormalSections A I a F r))
  map_one' := by rw [smulFormalSections_one, limMap_id]; rfl
  map_mul' r s := by rw [smulFormalSections_mul, limMap_comp']; rfl
  map_zero' := by rw [smulFormalSections_zero, limMap_zero]; rfl
  map_add' r s := by rw [smulFormalSections_add, limMap_add]; rfl

/-- Multiplication by `r` on the limit is the map induced by multiplication by `r` on the
inverse system of formal sections. -/
public theorem limFormalSectionsSmul_apply (r : A) :
    (limFormalSectionsSmul A I a F r).asHom = limMap (smulFormalSections A I a F r) :=
  rfl

/-! ### The comparison map is `A`-linear -/

/-- Reduction modulo `Iⁿ` on a neighbourhood commutes with multiplication by `A`. -/
public theorem projNearVanishing_comp_smul (V : OpensNearVanishing A I a) (n : ℕᵒᵖ) (r : A) :
    projNearVanishing A I a F V n ≫
        (((quotientSystemNearVanishing A I a F).obj n).smul (opensScalars A a V.openSet r)).asHom =
      (F.smul (opensScalars A a V.openSet r)).asHom ≫ projNearVanishing A I a F V n :=
  app_comp_smul (adicProj (idealSheafNearVanishing A I a) F n) (opensScalars A a V.openSet r)

/-- Extending a section of `F / Iⁿ F` from a neighbourhood of the formal locus back to all of
`U` commutes with multiplication by `A`. -/
public theorem inv_resNearVanishing_comp_smul (V : OpensNearVanishing A I a) (n : ℕᵒᵖ) (r : A) :
    inv (resNearVanishing A I a F V n) ≫ (smulFormalSections A I a F r).app n =
      (((quotientSystemNearVanishing A I a F).obj n).smul (opensScalars A a V.openSet r)).asHom ≫
        inv (resNearVanishing A I a F V n) := by
  have h : (smulFormalSections A I a F r).app n ≫
      resNearVanishing A I a F V n =
      resNearVanishing A I a F V n ≫
        (((quotientSystemNearVanishing A I a F).obj n).smul
          (opensScalars A a V.openSet r)).asHom := by
    have hres := Scheme.Modules.map_comp_smul
      (M := (quotientSystemNearVanishing A I a F).obj n)
      (homOfLE (le_top (a := V.openSet))) (opensScalars A a ⊤ r)
    rwa [opensScalars_res] at hres
  rw [IsIso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

/-- The comparison map `colim_V Γ(V, ℱ) ⟶ lim_n Γ(U, ℱ / Iⁿ ℱ)` commutes with the multiplication
by `A` on both sides induced by `A ⟶ Γ(U, 𝒪_U)`. -/
public theorem comparisonMap_comp_smul (r : A) :
    comparisonMap A I a F ≫ (limFormalSectionsSmul A I a F r).asHom =
      (colimSectionsSmul A I a F r).asHom ≫ comparisonMap A I a F := by
  refine colimit.hom_ext fun V ↦ ?_
  rw [colimSectionsSmul_apply, limFormalSectionsSmul_apply, ← Category.assoc,
    colimit_ι_comp_comparisonMap, ι_colimMap_assoc, colimit_ι_comp_comparisonMap]
  refine limit.hom_ext fun n ↦ ?_
  rw [Category.assoc, limMap_π, comparisonAt_π_assoc, Category.assoc, comparisonAt_π,
    inv_resNearVanishing_comp_smul, smulSectionsNearVanishing_app, ← Category.assoc,
    projNearVanishing_comp_smul]
  exact Category.assoc _ _ _

/-! ### The two sides as `A`-modules, and the comparison map between them -/

/-- The sections of `ℱ` near the formal locus `U ∩ V(I)`, as an `A`-module: the colimit
`colim_V Γ(V, ℱ)` with the multiplication by `A` induced by `A ⟶ Γ(U, 𝒪_U)`. -/
public def sectionsNearVanishingColimit : ModuleCat.{u} A :=
  ModuleCat.mkOfSMul (colimSectionsSmul A I a F)

/-- The formal sections of `ℱ` along `U ∩ V(I)`, as an `A`-module: the limit
`lim_n Γ(U, ℱ / Iⁿ ℱ)` with the multiplication by `A` induced by `A ⟶ Γ(U, 𝒪_U)`. -/
public def formalSectionsLimit : ModuleCat.{u} A :=
  ModuleCat.mkOfSMul (limFormalSectionsSmul A I a F)

/-- The comparison map `Stacks.Algebraization.comparisonMap` as a map of `A`-modules. -/
public def comparisonModuleMap :
    sectionsNearVanishingColimit A I a F ⟶ formalSectionsLimit A I a F :=
  ModuleCat.homMk (comparisonMap A I a F) (comparisonMap_comp_smul A I a F)

/-- The underlying map of abelian groups of the `A`-linear comparison map is
`Stacks.Algebraization.comparisonMap`. -/
public theorem forget₂_comparisonModuleMap :
    (forget₂ (ModuleCat.{u} A) Ab).map (comparisonModuleMap A I a F) = comparisonMap A I a F :=
  rfl

/-- The `A`-linear comparison map is an isomorphism exactly when the comparison map is. -/
public theorem isIso_comparisonModuleMap_iff :
    IsIso (comparisonModuleMap A I a F) ↔ IsIso (comparisonMap A I a F) := by
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  exact Iff.rfl

end Stacks.Algebraization

end

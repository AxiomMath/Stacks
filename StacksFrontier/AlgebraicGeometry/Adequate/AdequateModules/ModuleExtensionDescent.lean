module

public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineCechSheafCondition

/-!
# Faithfully flat descent for the module extensions on the algebras of a site

Let `A` be a ring and `P` a property of schemes cutting out a big site. The module extension
`B ↦ B ⊗[A] M` of an `A`-module `M` is a module-valued functor on the `A`-algebras whose spectra
belong to the site. This file proves the **sheaf condition for a finite family of such algebras
whose product is faithfully flat over the base**: it is degree-zero exactness of the Amitsur
complex of that product, which is [Stacks, Tag 023M] in degrees `−1` and `0`.

Nothing here is a topology: the statement is about one covering family at a time. It is the
algebraic input of [Stacks, Tag 06VP], where the sheaf condition for the induced topology on the
algebras of the site is obtained from it by refining an arbitrary covering sieve.

## Main definitions

* `Stacks.Adequate.siteModuleExtension` — the module extension `B ↦ B ⊗[A] M`, restricted to the
  algebras of the site.
* `Stacks.Adequate.siteAlgebraObj` and `Stacks.Adequate.siteAlgebraHom` — a ring whose spectrum
  belongs to the site, and an algebra map between two such, as an object and a morphism of the
  category of algebras of the site.
* `Stacks.Adequate.arrowAlgebra` — the algebra structure a morphism of algebras of the site puts
  on its target. This is what makes the hypotheses of the main result — the sheaf condition for a
  family given by morphisms of the site — expressible.

## Main results

* `Stacks.Adequate.isSheafFor_ofArrows_siteModuleExtension` — **the sheaf condition for a finite
  family of algebras of the site whose product is faithfully flat over the base.** The comparison
  of the sections over a member with the base change is the cancellation
  `Bᵢ ⊗[R₀] (R₀ ⊗[A] M) ≅ Bᵢ ⊗[A] M`, and the comparison over a pairwise tensor product is the
  same cancellation; `PresheafOfModules.exists_amitsurDiff₀_data` assembles them into the
  degree-zero Amitsur data and `PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀` turns that
  into the sheaf condition.
* `Stacks.Adequate.isSheafFor_ofArrows_siteModuleExtension'` — the same, for a family given by
  morphisms of the category of algebras of the site rather than by algebra structures.

## Implementation notes

The pairwise objects of the Amitsur data are the tensor products `Bᵢ ⊗[R₀] Bⱼ` themselves, and
their membership in the site is a hypothesis: the main result is about one family, and whether
the site is closed under these tensor products depends on the site.

The comparisons are built by hand rather than through
`PresheafOfModules.exists_pairBaseChange`, which would need the two algebra structures of
`Bᵢ ⊗[R₀] Bⱼ` over `Bᵢ` and over `Bⱼ` as instances at once; on the diagonal `i = j` those are two
different instances for one pair of types. The cancellation `coverPairCompare` needs neither.

## References

* [Stacks Project, Tag 06VP](https://stacks.math.columbia.edu/tag/06VP)
* [Stacks Project, Tag 023M](https://stacks.math.columbia.edu/tag/023M)
* [Stacks Project, Tag 06UT](https://stacks.math.columbia.edu/tag/06UT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe u m

namespace Stacks.Adequate

section Core

variable {A : Type u} [CommRing A] {P : ObjectProperty Scheme.{u}}

/-- The module extension `B ↦ B ⊗[A] M` of an `A`-module `M`, on the algebras of the site. -/
public noncomputable abbrev siteModuleExtension (M : ModuleCat.{max u m} A) :
    AdequateFunctor.ModuleValuedFunctorOn.{max u m}
      (AdequateFunctor.siteAlgebraInclusion A P) :=
  (AdequateFunctor.moduleExtensionFunctorOn.{max u m, u}
    (AdequateFunctor.siteAlgebraInclusion A P)).obj M

/-- An `A`-algebra `R` whose spectrum satisfies `P`, as an algebra of the site. -/
public abbrev siteAlgebraObj (R : Type u) [CommRing R] [Algebra A R]
    (h : P (Spec (CommRingCat.of R))) :
    AdequateFunctor.AlgebrasInSite A P := ⟨CommAlgCat.of A R, h⟩

/-- An `A`-algebra map `R →ₐ[A] S`, as a morphism of algebras of the site. -/
public abbrev siteAlgebraHom {R S : Type u} [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (hR : P (Spec (CommRingCat.of R))) (hS : P (Spec (CommRingCat.of S))) (φ : R →ₐ[A] S) :
    siteAlgebraObj (A := A) (P := P) R hR ⟶ siteAlgebraObj (A := A) (P := P) S hS :=
  ObjectProperty.homMk (CommAlgCat.ofHom φ)

/-- The module extension sends a morphism `φ : R ⟶ S` of algebras of the site to
`r ⊗ x ↦ φ r ⊗ x`. -/
public theorem siteModuleExtension_restrictₛₗ (M : ModuleCat.{max u m} A)
    {R S : Type u} [CommRing R] [CommRing S] [Algebra A R] [Algebra A S]
    (hR : P (Spec (CommRingCat.of R))) (hS : P (Spec (CommRingCat.of S))) (φ : R →ₐ[A] S)
    (r : R) (x : M) :
    (siteModuleExtension (P := P) M).restrictₛₗ (siteAlgebraHom hR hS φ).op.op (r ⊗ₜ[A] x) =
      φ r ⊗ₜ[A] x := rfl

section Family

variable {R₀ : Type u} [CommRing R₀] [Algebra A R₀]
  {ι : Type} {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)]
  [∀ i, Algebra R₀ (B i)] [∀ i, IsScalarTower A R₀ (B i)]

/-- The structure morphism of a member of the family, in the algebras of the site. -/
public abbrev coverMemberHom (hR₀ : P (Spec (CommRingCat.of R₀)))
    (hB : ∀ i, P (Spec (CommRingCat.of (B i)))) (i : ι) :
    siteAlgebraObj (A := A) (P := P) R₀ hR₀ ⟶ siteAlgebraObj (A := A) (P := P) (B i) (hB i) :=
  siteAlgebraHom hR₀ (hB i) ((Algebra.ofId R₀ (B i)).restrictScalars A)

/-- The comparison of the sections over a member with the base change. -/
public noncomputable abbrev coverMemberCompare (M : ModuleCat.{max u m} A) (i : ι) :
    TensorProduct R₀ (B i) (TensorProduct A R₀ M) ≃ₗ[B i] TensorProduct A (B i) M :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange A R₀ (B i) (B i) M

/-- The comparison `coverMemberCompare` on pure tensors: `b ⊗ (r ⊗ x) ↦ (r • b) ⊗ x`. -/
public theorem coverMemberCompare_tmul (M : ModuleCat.{max u m} A) (i : ι) (b : B i) (r : R₀)
    (x : M) :
    coverMemberCompare M (B := B) i (b ⊗ₜ[R₀] (r ⊗ₜ[A] x)) = (r • b) ⊗ₜ[A] x := by
  simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

/-- The comparison `coverMemberCompare` on `1 ⊗ n` is the restriction of the module extension
along the structure morphism of the member. -/
public theorem coverMemberCompare_one_tmul (M : ModuleCat.{max u m} A)
    (hR₀ : P (Spec (CommRingCat.of R₀)))
    (hB : ∀ i, P (Spec (CommRingCat.of (B i)))) (i : ι) (n : TensorProduct A R₀ M) :
    coverMemberCompare M (B := B) i ((1 : B i) ⊗ₜ[R₀] n) =
      (siteModuleExtension (P := P) M).restrictₛₗ (coverMemberHom hR₀ hB i).op.op n := by
  induction n using TensorProduct.inductionOn with
  | tmul r x =>
      rw [siteModuleExtension_restrictₛₗ, coverMemberCompare_tmul]
      simp [Algebra.smul_def, Algebra.ofId_apply]
  | add p q hp hq =>
      rw [TensorProduct.tmul_add, map_add, hp, hq]
      exact (map_add ((siteModuleExtension (P := P) M).restrictₛₗ
        (coverMemberHom hR₀ hB i).op.op) p q).symm

/-- The tensor product of two members, as an algebra of the site. -/
public abbrev coverPairAlgebra
    (hPb : ∀ i j, P (Spec (CommRingCat.of (TensorProduct R₀ (B i) (B j)))))
    (i j : ι) : AdequateFunctor.AlgebrasInSite A P :=
  siteAlgebraObj (A := A) (P := P) (TensorProduct R₀ (B i) (B j)) (hPb i j)

/-- The first inclusion into the tensor product of two members. -/
public abbrev coverPairIncl₁ (hB : ∀ i, P (Spec (CommRingCat.of (B i))))
    (hPb : ∀ i j, P (Spec (CommRingCat.of (TensorProduct R₀ (B i) (B j))))) (i j : ι) :
    siteAlgebraObj (A := A) (P := P) (B i) (hB i) ⟶ coverPairAlgebra (A := A) (P := P) hPb i j :=
  siteAlgebraHom (hB i) (hPb i j) Algebra.TensorProduct.includeLeft

/-- The second inclusion into the tensor product of two members. -/
public abbrev coverPairIncl₂ (hB : ∀ i, P (Spec (CommRingCat.of (B i))))
    (hPb : ∀ i j, P (Spec (CommRingCat.of (TensorProduct R₀ (B i) (B j))))) (i j : ι) :
    siteAlgebraObj (A := A) (P := P) (B j) (hB j) ⟶ coverPairAlgebra (A := A) (P := P) hPb i j :=
  siteAlgebraHom (hB j) (hPb i j) (Algebra.TensorProduct.includeRight.restrictScalars A)

/-- The two composites `R₀ ⟶ B i ⟶ B i ⊗[R₀] B j` and `R₀ ⟶ B j ⟶ B i ⊗[R₀] B j` agree. -/
public theorem coverMemberHom_comp_pairIncl (hR₀ : P (Spec (CommRingCat.of R₀)))
    (hB : ∀ i, P (Spec (CommRingCat.of (B i))))
    (hPb : ∀ i j, P (Spec (CommRingCat.of (TensorProduct R₀ (B i) (B j))))) (i j : ι) :
    coverMemberHom hR₀ hB i ≫ coverPairIncl₁ (A := A) (P := P) hB hPb i j =
      coverMemberHom hR₀ hB j ≫ coverPairIncl₂ (A := A) (P := P) hB hPb i j := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  refine AlgHom.ext fun r => ?_
  change (algebraMap R₀ (B i) r) ⊗ₜ[R₀] (1 : B j) = (1 : B i) ⊗ₜ[R₀] (algebraMap R₀ (B j) r)
  rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  exact TensorProduct.smul_tmul _ _ _

/-- The comparison of the sections over a pairwise tensor product with the base change. -/
public noncomputable abbrev coverPairCompare (M : ModuleCat.{max u m} A) (i j : ι) :
    TensorProduct R₀ (TensorProduct R₀ (B i) (B j)) (TensorProduct A R₀ M) ≃ₗ[
        TensorProduct R₀ (B i) (B j)]
      TensorProduct A (TensorProduct R₀ (B i) (B j)) M :=
  TensorProduct.AlgebraTensorModule.cancelBaseChange A R₀ (TensorProduct R₀ (B i) (B j))
    (TensorProduct R₀ (B i) (B j)) M

/-- The comparison `coverPairCompare` on pure tensors: `d ⊗ (r ⊗ x) ↦ (r • d) ⊗ x`. -/
public theorem coverPairCompare_tmul (M : ModuleCat.{max u m} A) (i j : ι)
    (d : TensorProduct R₀ (B i) (B j)) (r : R₀) (x : M) :
    coverPairCompare M (B := B) i j (d ⊗ₜ[R₀] (r ⊗ₜ[A] x)) = (r • d) ⊗ₜ[A] x := by
  simp [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul]

/-- The comparisons are compatible with the first inclusion `B i ⟶ B i ⊗[R₀] B j`. -/
public theorem coverPairCompare_nat₁ (M : ModuleCat.{max u m} A)
    (hB : ∀ i, P (Spec (CommRingCat.of (B i))))
    (hPb : ∀ i j, P (Spec (CommRingCat.of (TensorProduct R₀ (B i) (B j))))) (i j : ι)
    (b : B i) (n : TensorProduct A R₀ M) :
    (siteModuleExtension (P := P) M).restrictₛₗ (coverPairIncl₁ (A := A) (P := P) hB hPb i j).op.op
        (coverMemberCompare M (B := B) i (b ⊗ₜ[R₀] n)) =
      coverPairCompare M (B := B) i j ((b ⊗ₜ[R₀] (1 : B j)) ⊗ₜ[R₀] n) := by
  induction n using TensorProduct.inductionOn with
  | tmul r x =>
      rw [coverMemberCompare_tmul, siteModuleExtension_restrictₛₗ, coverPairCompare_tmul,
        TensorProduct.smul_tmul']
      rfl
  | add p q hp hq =>
      rw [TensorProduct.tmul_add, map_add, TensorProduct.tmul_add, map_add, ← hp, ← hq]
      exact map_add _ _ _

/-- The comparisons are compatible with the second inclusion `B j ⟶ B i ⊗[R₀] B j`. -/
public theorem coverPairCompare_nat₂ (M : ModuleCat.{max u m} A)
    (hB : ∀ i, P (Spec (CommRingCat.of (B i))))
    (hPb : ∀ i j, P (Spec (CommRingCat.of (TensorProduct R₀ (B i) (B j))))) (i j : ι)
    (b : B j) (n : TensorProduct A R₀ M) :
    (siteModuleExtension (P := P) M).restrictₛₗ (coverPairIncl₂ (A := A) (P := P) hB hPb i j).op.op
        (coverMemberCompare M (B := B) j (b ⊗ₜ[R₀] n)) =
      coverPairCompare M (B := B) i j (((1 : B i) ⊗ₜ[R₀] b) ⊗ₜ[R₀] n) := by
  induction n using TensorProduct.inductionOn with
  | tmul r x =>
      rw [coverMemberCompare_tmul, siteModuleExtension_restrictₛₗ, coverPairCompare_tmul,
        show (r • ((1 : B i) ⊗ₜ[R₀] b)) = (1 : B i) ⊗ₜ[R₀] (r • b) from by
          rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul]]
      rfl
  | add p q hp hq =>
      rw [TensorProduct.tmul_add, map_add, TensorProduct.tmul_add, map_add, ← hp, ← hq]
      exact map_add _ _ _

/-- **The sheaf condition for a jointly faithfully flat finite family of algebras of the
site**, for a module extension. -/
public theorem isSheafFor_ofArrows_siteModuleExtension (M : ModuleCat.{max u m} A) [Finite ι]
    (hR₀ : P (Spec (CommRingCat.of R₀)))
    (hB : ∀ i, P (Spec (CommRingCat.of (B i))))
    (hPb : ∀ i j, P (Spec (CommRingCat.of (TensorProduct R₀ (B i) (B j)))))
    [Module.FaithfullyFlat R₀ (∀ i, B i)] :
    Presieve.IsSheafFor ((siteModuleExtension (P := P) M).presheaf ⋙ forget AddCommGrpCat.{max u m})
      (Presieve.ofArrows
        (fun i => (op (siteAlgebraObj (A := A) (P := P) (B i) (hB i)) :
          (AdequateFunctor.AlgebrasInSite A P)ᵒᵖ))
        (fun i => (coverMemberHom hR₀ hB i).op)) := by
  obtain ⟨eW, eV, hbij, hone, hinj, hdd⟩ :=
    PresheafOfModules.exists_amitsurDiff₀_data (N := siteModuleExtension (P := P) M)
      (fun i => (coverMemberHom hR₀ hB i).op)
      (fun i j => (coverPairIncl₁ (A := A) (P := P) hB hPb i j).op)
      (fun i j => (coverPairIncl₂ (A := A) (P := P) hB hPb i j).op)
      R₀ B (fun i => (coverMemberCompare M (B := B) i).toAddEquiv)
      (fun i n => coverMemberCompare_one_tmul M hR₀ hB i n)
      (fun i j => (coverPairCompare M (B := B) i j).toAddEquiv.toAddMonoidHom)
      (fun i j => (coverPairCompare M (B := B) i j).injective)
      (fun i j b n => coverPairCompare_nat₁ M hB hPb i j b n)
      (fun i j b n => coverPairCompare_nat₂ M hB hPb i j b n)
  refine PresheafOfModules.isSheafFor_ofArrows_of_amitsurDiff₀
    (fun i => (coverMemberHom hR₀ hB i).op) R₀ (∀ i, B i)
    (fun i j => op (coverPairAlgebra (A := A) (P := P) hPb i j))
    (fun i j => (coverPairIncl₁ (A := A) (P := P) hB hPb i j).op)
    (fun i j => (coverPairIncl₂ (A := A) (P := P) hB hPb i j).op)
    (fun i j => ?_) eW hbij hone eV hinj hdd
  rw [← op_comp, ← op_comp, coverMemberHom_comp_pairIncl hR₀ hB hPb i j]

end Family

end Core

section Bridge

variable {A : Type u} [CommRing A] {P : ObjectProperty Scheme.{u}}

/-- The algebra structure that a morphism of algebras of the site puts on its target. -/
public abbrev arrowAlgebra {W W' : AdequateFunctor.AlgebrasInSite A P} (g : W ⟶ W') :
    Algebra (W.obj : Type u) (W'.obj : Type u) := g.hom.hom.toRingHom.toAlgebra

/-- The algebra structure of `arrowAlgebra` is compatible with the `A`-algebra structures. -/
public theorem arrowAlgebra_isScalarTower {W W' : AdequateFunctor.AlgebrasInSite A P} (g : W ⟶ W') :
    letI := arrowAlgebra g
    IsScalarTower A (W.obj : Type u) (W'.obj : Type u) := by
  let := arrowAlgebra g
  refine IsScalarTower.of_algebraMap_eq fun a => ?_
  exact (g.hom.hom.commutes a).symm

/-- A morphism of algebras of the site is the morphism of the algebra map `Algebra.ofId` of
the algebra structure it defines. -/
public theorem siteAlgebraHom_ofId {W W' : AdequateFunctor.AlgebrasInSite A P} (g : W ⟶ W') :
    letI := arrowAlgebra g
    siteAlgebraHom (A := A) (P := P) W.property W'.property
        ((Algebra.ofId (W.obj : Type u) (W'.obj : Type u)).restrictScalars A) = g := rfl

/-- **The sheaf condition for a jointly faithfully flat finite family**, stated for morphisms of
algebras of the site. -/
public theorem isSheafFor_ofArrows_siteModuleExtension' (M : ModuleCat.{max u m} A) {ι : Type}
    [Finite ι]
    {X : AdequateFunctor.AlgebrasInSite A P} {Y : ι → AdequateFunctor.AlgebrasInSite A P}
    (q : ∀ i, X ⟶ Y i)
    (hPb : letI := fun i => arrowAlgebra (q i)
           ∀ i j, P (Spec (CommRingCat.of
             (TensorProduct (X.obj : Type u) ((Y i).obj : Type u) ((Y j).obj : Type u)))))
    (hff : letI := fun i => arrowAlgebra (q i)
           Module.FaithfullyFlat (X.obj : Type u) (∀ i, ((Y i).obj : Type u))) :
    Presieve.IsSheafFor ((siteModuleExtension (P := P) M).presheaf ⋙ forget AddCommGrpCat.{max u m})
      (Presieve.ofArrows (fun i => (op (Y i) : (AdequateFunctor.AlgebrasInSite A P)ᵒᵖ))
        (fun i => (q i).op)) := by
  let : ∀ i, Algebra (X.obj : Type u) ((Y i).obj : Type u) := fun i => arrowAlgebra (q i)
  let : ∀ i, IsScalarTower A (X.obj : Type u) ((Y i).obj : Type u) :=
    fun i => arrowAlgebra_isScalarTower (q i)
  let := hff
  exact isSheafFor_ofArrows_siteModuleExtension M (B := fun i => ((Y i).obj : Type u))
    X.property (fun i => (Y i).property) hPb

end Bridge

end Stacks.Adequate



end

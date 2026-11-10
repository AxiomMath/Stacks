module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.Algebra.Module.Adequate.Defs
public import StacksFrontier.RingTheory.Flat.UniversallyInjective

/-!
# Lifting an additive transformation to a module map, at independent universes

This file re-proves the lifting criterion of Tag 06V5 for module-valued functors whose algebra
carriers and whose values live in universes independent of the base ring: the algebras are
objects of `CommAlgCat.{max u v} A` and the values lie in `Type (max u v w)`, so that the
statement applies to `AdequateFunctor.ModuleValuedFunctor.{max u v w, v} A`.

The mathematical content is unchanged.  An additive natural transformation of the underlying
presheaves of abelian groups which is semilinear for *units* of the structure ring is already
semilinear for every scalar `b`: after adjoining a root `r` of `X ^ 2 - b * X + 1` the element
`b` becomes the sum of the two units `r` and `b - r`, and the base-change hypothesis on the
target makes the resulting descent along the faithfully flat map `B → B[r]` legitimate.
-/

@[expose] public section

namespace AdequateFunctor.Laurent

section

open CategoryTheory Opposite

universe w v u

/-- The functor sending an `A`-algebra to its underlying commutative ring, with the algebra
carriers in a universe independent of the base ring. The double opposite presents it in the
variance required by `PresheafOfModules`. -/
public abbrev algebraCommRingDiagramLarge (A : Type u) [CommRing A] :
    ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ ⥤ CommRingCat.{max u v} :=
  unopUnop (CommAlgCat.{max u v} A) ⋙ forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}

attribute [local instance 0] CategoryTheory.ReflQuiver.toQuiver

/-- An additive natural transformation of module-valued functors which commutes
with multiplication by units is induced by a morphism of module-valued
functors, provided the target commutes with flat base change. Independent-universe form:
the algebras are objects of `CommAlgCat.{max u v} A` and the module values live in
`Type (max u v w)`. -/
public theorem naturalTransformation_lifts_of_units_of_flatBaseChange_large
    (A : Type u) [CommRing A]
    (F G : PresheafOfModules.{max u v w} (algebraRingDiagram.{v} A))
    (φ : F.presheaf ⟶ G.presheaf)
    (hunit : ∀ (B : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ)
      (x : F.obj B) (a : Units ((algebraRingDiagram.{v} A).obj B)),
      φ.app B ((a : (algebraRingDiagram.{v} A).obj B) • x) =
        (a : (algebraRingDiagram.{v} A).obj B) • (φ.app B x : G.obj B))
    (hbase : ∀ {B B' : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ} (f : B ⟶ B'),
      letI : Algebra ((algebraCommRingDiagramLarge.{v} A).obj B)
          ((algebraCommRingDiagramLarge.{v} A).obj B') :=
        ((algebraCommRingDiagramLarge.{v} A).map f).hom.toAlgebra
      Module.Flat ((algebraCommRingDiagramLarge.{v} A).obj B)
          ((algebraCommRingDiagramLarge.{v} A).obj B') →
        ∃ e : TensorProduct ((algebraCommRingDiagramLarge.{v} A).obj B)
              ((algebraCommRingDiagramLarge.{v} A).obj B') (G.obj B) ≃ₗ[
                (algebraCommRingDiagramLarge.{v} A).obj B'] G.obj B',
          ∀ x : G.obj B,
            e ((1 : (algebraCommRingDiagramLarge.{v} A).obj B') ⊗ₜ[
              (algebraCommRingDiagramLarge.{v} A).obj B] x) = G.map f x) :
    ∃ ψ : F ⟶ G,
      (PresheafOfModules.toPresheaf (algebraRingDiagram.{v} A)).map ψ = φ := by
  let ψ : F ⟶ G :=
    { app := fun B ↦
        ModuleCat.ofHom
        { toFun := φ.app B
          map_add' := (φ.app B).hom.map_add
          map_smul' := by
            intro b x
            rcases B with ⟨B⟩
            rcases B with ⟨B⟩
            change B at b
            by_cases hR : Nontrivial B
            swap
            · have : Subsingleton B := not_nontrivial_iff_subsingleton.mp hR
              let : Subsingleton (G.obj (Opposite.op (Opposite.op B))) :=
                Module.subsingleton B _
              exact Subsingleton.elim _ _
            let : Nontrivial B := hR
            let p : Polynomial B := Polynomial.X ^ 2 -
              Polynomial.C b * Polynomial.X + 1
            have hpdeg : p.IsMonicOfDegree 2 := Polynomial.isMonicOfDegree_sub_add_two b 1
            have hp : p.Monic := hpdeg.monic
            let S := AdjoinRoot p
            let algAS : Algebra A S :=
              ((algebraMap B S).comp (algebraMap A B)).toAlgebra
            let g : B →ₐ[A] S :=
              { algebraMap B S with commutes' := fun _ ↦ rfl }
            let B' : ((CommAlgCat.{max u v} A)ᵒᵖ)ᵒᵖ :=
              Opposite.op (Opposite.op (CommAlgCat.of A S))
            let f : Opposite.op (Opposite.op B) ⟶ B' :=
              (ConcreteCategory.ofHom g : B ⟶ CommAlgCat.of A S).op.op
            let r : S := AdjoinRoot.root p
            have hr : r * (algebraMap B S b - r) = 1 := by
              have hroot : r ^ 2 - algebraMap B S b * r + 1 = 0 := by
                have h : Polynomial.aeval r p = 0 :=
                  (AdjoinRoot.aeval_eq p).trans AdjoinRoot.mk_self
                simpa only [p, map_add, map_sub, map_pow, map_mul,
                  Polynomial.aeval_X, Polynomial.aeval_C, map_one] using h
              rw [mul_sub]
              linear_combination -hroot
            have hr' : (algebraMap B S b - r) * r = 1 := by simpa only [mul_comm] using hr
            let ur : Units S := ⟨r, algebraMap B S b - r, hr, hr'⟩
            let us : Units S := ⟨algebraMap B S b - r, r, hr', hr⟩
            have hsum : (ur : S) + (us : S) = algebraMap B S b := by dsimp [ur, us]; abel
            have hff₀ : (algebraMap B S).FaithfullyFlat := by
              let : Module.Free B S := hp.free_adjoinRoot
              let : Nontrivial S :=
                (AdjoinRoot.of.injective_of_monic_of_degree_pos hp (by
                  rw [Polynomial.degree_eq_natDegree hp.ne_zero, hpdeg.natDegree_eq]
                  norm_num)).nontrivial
              rw [RingHom.faithfullyFlat_algebraMap_iff]
              infer_instance
            let q := ((algebraCommRingDiagramLarge.{v} A).map f).hom
            have hq : q = algebraMap B S := rfl
            have hff : q.FaithfullyFlat := hff₀
            let : Algebra ((algebraCommRingDiagramLarge.{v} A).obj
                (Opposite.op (Opposite.op B)))
                ((algebraCommRingDiagramLarge.{v} A).obj B') := q.toAlgebra
            obtain ⟨e, he⟩ := hbase f hff.flat
            have hinj : Function.Injective (fun y : G.obj (Opposite.op (Opposite.op B)) ↦
                e (1 ⊗ₜ[↑((algebraCommRingDiagramLarge.{v} A).obj
                  (Opposite.op (Opposite.op B)))] y)) := e.injective.comp
              (faithfullyFlat_tensor_mk_injective
                q hff (G.obj (Opposite.op (Opposite.op B))))
            have hGinj : Function.Injective (G.map f) := fun y z hyz =>
              hinj (by dsimp only; rwa [he y, he z])
            have hnat (z : F.obj (Opposite.op (Opposite.op B))) :
                φ.app B' (F.map f z) =
                  G.map f (φ.app (Opposite.op (Opposite.op B)) z) :=
              ConcreteCategory.congr_hom (φ.naturality f) z
            apply hGinj
            rw [← hnat (b • x), F.map_smul]
            simp only [RingHom.id_apply]
            let y : G.obj (Opposite.op (Opposite.op B)) :=
              φ.app (Opposite.op (Opposite.op B)) x
            change φ.app B' ((algebraRingDiagram.{v} A).map f b • F.map f x) =
              G.map f (b • y)
            rw [G.map_smul]
            let φ' : F.obj B' →+ G.obj B' :=
              { toFun := fun z ↦ φ.app B' z
                map_zero' := (φ.app B').hom.map_zero
                map_add' := (φ.app B').hom.map_add }
            change φ' (q b • F.map f x) = q b • G.map f y
            rw [hq]
            -- `φ'` bundles `φ.app B'` so that the scalar action on `G.obj B'`
            -- resolves; the cost is that `hunit` and `hnat`, stated for
            -- `φ.app B'`, no longer match syntactically under its coercion, and
            -- their scalar actions come from a different (defeq) instance path.
            -- Restating each step in the goal's own spelling and discharging it
            -- by a *term* lets definitional unification absorb that.
            have hunit' (w : Units S) :
                φ' ((w : S) • F.map f x) = (w : S) • φ' (F.map f x) :=
              hunit B' (F.map f x) w
            have hu : φ' ((algebraMap B S b) • F.map f x) =
                (algebraMap B S b) • φ' (F.map f x) := by
              rw [← hsum, add_smul, add_smul]
              exact (φ'.map_add _ _).trans (congrArg₂ _ (hunit' ur) (hunit' us))
            have hnat' : φ' (F.map f x) = G.map f y := hnat x
            rw [hu, hnat']
            rfl }
      naturality := by
        intro B B' f
        ext x
        exact CategoryTheory.congr_fun (φ.naturality f) x }
  exact ⟨ψ, rfl⟩

end

end AdequateFunctor.Laurent

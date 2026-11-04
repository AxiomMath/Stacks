module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsNoetherian
public import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A limit preserving functor of points on the locally Noetherian objects (Stacks 0GE4)

Let `S` be a locally Noetherian scheme and let `X` be a locally Noetherian object of `Sch/S`. If
the functor of points of `X`, taken on the full subcategory `(Noetherian/S)` of locally Noetherian
objects, takes directed inverse limits of affine objects of that subcategory to filtered colimits,
then `X` is locally of finite presentation over `S`.

This is Stacks 0GE4 in the vocabulary of
`AlgebraicGeometry.ExtendingFunctors.IsLocallyNoetherianOver`, i.e. for the full subcategory of
`Over S` rather than for a full subcategory of a big site with a cardinal cutoff. No condition of
membership in a site is involved, so the approximating inverse system can be used as it stands.

## Main results

* **Stacks 0GE4** is the theorem
  `locallyOfFinitePresentation_of_preservesAffineLimitsOnSubcategory`
  of the namespace `AlgebraicGeometry.ExtendingFunctors`.

## Implementation notes

The proof is the source's. On an affine chart `V ⊆ X` lying over an affine chart `U ⊆ S`, write the
ring `A = Γ(X, V)` as a directed colimit of `R = Γ(S, U)`-algebras `G l` of finite presentation,
which is Stacks 00QN in the form `Algebra.exists_directedSystem_finitePresentation_lift_bijective`.
Since `S` is locally Noetherian, `R` is Noetherian, so each `G l`, being of finite type over `R`,
is Noetherian and `Spec (G l)` is a locally Noetherian object of `Sch/S`; `Spec A` is one too, `X`
being locally Noetherian. Applying the spectrum functor turns the colimit of rings into a directed
inverse limit of affine objects of `(Noetherian/S)`, and the hypothesis factors the chart
`Spec A ⟶ X` through one stage. Shrinking the index once more, by
`AlgebraicGeometry.exists_map_eq_top`, so that the factorisation lands inside `V`, that stage's map
is a section of the colimit map, so `A` is a retract of a finitely presented `R`-algebra and
therefore finitely presented itself. The retract step is
`Stacks.AlgebraCategory.Presentability.finitePresentation_of_retract`.

## References

* [Stacks Project, Tag 0GE4](https://stacks.math.columbia.edu/tag/0GE4)
* [Stacks Project, Tag 00QN](https://stacks.math.columbia.edu/tag/00QN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ExtendingFunctors

universe w u

variable {S : Scheme.{u}}

/-- **Stacks 0GE4.** Let `S` be a locally Noetherian scheme and let `X` be a locally Noetherian
object of `Sch/S`. If the functor of points of `X` on the full subcategory of locally Noetherian
objects takes directed inverse limits of affine objects to filtered colimits, then `X` is locally
of finite presentation over `S`. -/
@[ega "IV 17.3.2" "special case"]
theorem locallyOfFinitePresentation_of_preservesAffineLimitsOnSubcategory
    [IsLocallyNoetherian S] (X : (IsLocallyNoetherianOver (S := S)).FullSubcategory)
    (hX : PreservesAffineLimitsOnSubcategory (IsLocallyNoetherianOver (S := S))
      (uliftYoneda.{max w (u + 1)}.obj X)) :
    LocallyOfFinitePresentation X.obj.hom := by
  classical
  have hXN : IsLocallyNoetherian X.obj.left := X.property
  rw [locallyOfFinitePresentation_iff]
  intro U hU V hV e
  let R : CommRingCat.{u} := CommRingCat.of Γ(S, U)
  let A : CommRingCat.{u} := CommRingCat.of Γ(X.obj.left, V)
  let α : R ⟶ A := X.obj.hom.appLE U V e
  let : Algebra ↑R ↑A := α.hom.toAlgebra
  have hRnoeth : IsNoetherianRing ↑R := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let : IsNoetherianRing R := hRnoeth
  obtain ⟨Λ, hpo, hnon, hdir, G, hComm, hAlg, q, hDS, g, hg, hfp, -, hbij⟩ :=
    Algebra.exists_directedSystem_finitePresentation_lift_bijective ↑R ↑A
  let : PartialOrder Λ := hpo
  let : Nonempty Λ := hnon
  let : IsDirectedOrder Λ := hdir
  let : ∀ l, CommRing (G l) := hComm
  let : ∀ l, Algebra ↑R (G l) := hAlg
  let : DirectedSystem G (fun i j h ↦ ⇑(q i j h)) := hDS
  have hstageNoeth (l : Λ) : IsLocallyNoetherian (Spec (CommRingCat.of (G l))) := by
    have : Algebra.FiniteType ↑R (G l) := inferInstance
    have : IsNoetherianRing (G l) := Algebra.FiniteType.isNoetherianRing ↑R (G l)
    exact isLocallyNoetherian_Spec.mpr inferInstance
  have hsourceNoeth : IsLocallyNoetherian (Spec A) := by
    have : IsNoetherianRing Γ(X.obj.left, V) := hXN.component_noetherian ⟨V, hV⟩
    exact isLocallyNoetherian_Spec.mpr inferInstance
  -- The directed system of finitely presented algebras and its colimit.
  let D₀ : Λ ⥤ CommRingCat.{u} :=
    { obj l := CommRingCat.of (G l)
      map {i j} h := CommRingCat.ofHom (q i j h.le).toRingHom
      map_id i := by ext x; exact DirectedSystem.map_self (f := fun i j h ↦ ⇑(q i j h)) x
      map_comp {i j k} hij hjk := by
        ext x
        exact (DirectedSystem.map_map (f := fun i j h ↦ ⇑(q i j h)) hij.le hjk.le x).symm }
  let c₀ : Cocone D₀ :=
    { pt := CommRingCat.of A
      ι :=
        { app l := CommRingCat.ofHom (g l).toRingHom
          naturality i j h := by ext x; exact hg i j h.le x } }
  have hc₀ : IsColimit c₀ := by
    let cInf : Cocone D₀ :=
      { pt := CommRingCat.of (DirectLimit G q)
        ι :=
          { app l := CommRingCat.ofHom (DirectLimit.Algebra.of G q l).toRingHom
            naturality i j h := by
              ext x
              exact DirectLimit.Algebra.of_f (f := q) h.le x } }
    have hcInf : IsColimit cInf := by
      refine { desc := ?_, fac := ?_, uniq := ?_ }
      · intro t
        exact CommRingCat.ofHom <| DirectLimit.Ring.lift G
          q ↑t.pt (fun l ↦ (t.ι.app l).hom)
          (by intro i j h x; exact congr($(t.w (homOfLE h)).hom x))
      · intro t l
        ext x
        rfl
      · intro t m hm
        apply CommRingCat.hom_ext
        apply DirectLimit.Ring.hom_ext
        intro l
        ext y
        exact congr($(hm l).hom y)
    exact hcInf.ofIsoColimit <| Cocone.ext
      (RingEquiv.ofBijective
        (DirectLimit.Algebra.lift G q A g hg).toRingHom hbij).toCommRingCatIso
      (by intro l; ext x; rfl)
  -- The inverse system of affine schemes and its limit.
  let Z : Λᵒᵖ ⥤ Scheme.{u} := D₀.op ⋙ Scheme.Spec
  let cZ : Cone Z := Scheme.Spec.mapCone c₀.op
  have hcZ : IsLimit cZ := isLimitOfPreserves Scheme.Spec hc₀.op
  have hBase {B C : Type u} [CommRing B] [CommRing C] [Algebra ↑R B] [Algebra ↑R C]
      (f : B →ₐ[↑R] C) :
      Scheme.Spec.map (op (CommRingCat.ofHom f.toRingHom)) ≫
        Scheme.Spec.map (op (CommRingCat.ofHom (algebraMap ↑R B))) =
        Scheme.Spec.map (op (CommRingCat.ofHom (algebraMap ↑R C))) := by
    rw [← Scheme.Spec.map_comp]
    refine congrArg Scheme.Spec.map (congrArg op ?_)
    ext r
    exact f.commutes r
  -- The inverse system in `Sch/S`.
  let s : Z ⟶ (Functor.const Λᵒᵖ).obj S :=
    { app i := Scheme.Spec.map (op (CommRingCat.ofHom (algebraMap ↑R (G i.unop)))) ≫ hU.fromSpec
      naturality := by
        intro i j m
        dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
        rw [Category.comp_id, ← Category.assoc]
        exact congrArg (fun a => a ≫ hU.fromSpec) (hBase (q _ _ m.unop.le)) }
  let p : cZ.pt ⟶ S := Scheme.Spec.map (op α) ≫ hU.fromSpec
  have hp (i : Λᵒᵖ) : cZ.π.app i ≫ s.app i = p := by
    dsimp only [s, p]
    rw [← Category.assoc]
    exact congrArg (fun a => a ≫ hU.fromSpec) (hBase (g i.unop))
  let DOver : Λᵒᵖ ⥤ Over S := Over.lift Z s
  let cOver : Cone DOver := Over.liftCone Z s cZ p hp
  have hcOver : IsLimit cOver := Over.isLimitLiftCone Z s cZ p hp hcZ
  -- The inverse system in the locally Noetherian subcategory.
  let D : Λᵒᵖ ⥤ (IsLocallyNoetherianOver (S := S)).FullSubcategory :=
    { obj i := ⟨DOver.obj i, hstageNoeth i.unop⟩
      map φ := ObjectProperty.homMk (DOver.map φ)
      map_id i := by apply ObjectProperty.hom_ext; exact DOver.map_id i
      map_comp φ ψ := by apply ObjectProperty.hom_ext; exact DOver.map_comp φ ψ }
  let c : Cone D :=
    { pt := ⟨cOver.pt, hsourceNoeth⟩
      π :=
        { app i := ObjectProperty.homMk (cOver.π.app i)
          naturality i j φ := by apply ObjectProperty.hom_ext; exact (cOver.w φ).symm } }
  have hc : IsLimit ((IsLocallyNoetherianOver (S := S)).ι.mapCone c) := hcOver
  have hAffineZ (i : Λᵒᵖ) : IsAffine (Z.obj i) := by
    change IsAffine (Spec (CommRingCat.of (G i.unop)))
    infer_instance
  let {i j : Λᵒᵖ} (φ : i ⟶ j) : IsAffineHom (Z.map φ) := by
    have hi := hAffineZ i
    have hj := hAffineZ j
    infer_instance
  -- The chart, as a morphism of the subcategory out of the limit.
  have hfVw : hV.fromSpec ≫ X.obj.hom = Scheme.Spec.map (op α) ≫ hU.fromSpec := by
    simpa using (IsAffineOpen.SpecMap_appLE_fromSpec X.obj.hom hU hV e).symm
  let fV : c.pt ⟶ X := ObjectProperty.homMk (Over.homMk hV.fromSpec hfVw)
  obtain ⟨hcol⟩ := hX Λ D hAffineZ c hc
  obtain ⟨i, y, hy⟩ :=
    Types.jointly_surjective_of_isColimit hcol (ULift.up fV)
  have hyeq : c.π.app i.unop ≫ y.down = fV := congrArg ULift.down hy
  -- Transport to schemes and shrink so that the factorisation lands in the chart.
  let F : (IsLocallyNoetherianOver (S := S)).FullSubcategory ⥤ Scheme.{u} :=
    (IsLocallyNoetherianOver (S := S)).ι ⋙ Over.forget S
  let aI : Z.obj i.unop ⟶ X.obj.left := F.map y.down
  have hmScheme : cZ.π.app i.unop ≫ aI = hV.fromSpec := by
    have h := congrArg (fun r => F.map r) hyeq
    rw [Functor.map_comp] at h
    exact h
  have hpre : cZ.π.app i.unop ⁻¹ᵁ (aI ⁻¹ᵁ V) = ⊤ := by
    rw [← Scheme.Hom.comp_preimage, hmScheme]
    exact hV.fromSpec_preimage_self
  obtain ⟨k, fki, hkV⟩ := exists_map_eq_top Z cZ hcZ (aI ⁻¹ᵁ V) hpre (i := i.unop)
  let aK : Z.obj k ⟶ X.obj.left := Z.map fki ≫ aI
  have haK : aK ⁻¹ᵁ V = ⊤ := hkV
  have hrange : Set.range aK ⊆ Set.range hV.fromSpec := by
    rw [hV.range_fromSpec, Set.range_subset_iff]
    intro x
    have hx : x ∈ aK ⁻¹ᵁ V := by rw [haK]; trivial
    exact (Scheme.Hom.mem_preimage aK).mp hx
  let aKV : Z.obj k ⟶ Spec A := IsOpenImmersion.lift hV.fromSpec aK hrange
  have haKV : aKV ≫ hV.fromSpec = aK := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨φ, hφ⟩ := Scheme.Spec.map_surjective aKV
  let φR : A ⟶ CommRingCat.of (G k.unop) := φ.unop
  let β : R ⟶ CommRingCat.of (G k.unop) :=
    CommRingCat.ofHom (algebraMap ↑R (G k.unop))
  -- The factorisation is a section of the colimit map.
  have hIf : aI ≫ X.obj.hom = Scheme.Spec.map (op (CommRingCat.ofHom
      (algebraMap ↑R (G i.unop.unop)))) ≫ hU.fromSpec :=
    Over.w ((IsLocallyNoetherianOver (S := S)).ι.map y.down)
  have hKf : aK ≫ X.obj.hom = Scheme.Spec.map (op β) ≫ hU.fromSpec := by
    calc
      aK ≫ X.obj.hom = Z.map fki ≫ (aI ≫ X.obj.hom) := Category.assoc _ _ _
      _ = Z.map fki ≫ (Scheme.Spec.map (op (CommRingCat.ofHom
          (algebraMap ↑R (G i.unop.unop)))) ≫ hU.fromSpec) :=
          congrArg (fun r => Z.map fki ≫ r) hIf
      _ = (Z.map fki ≫ Scheme.Spec.map (op (CommRingCat.ofHom
          (algebraMap ↑R (G i.unop.unop))))) ≫ hU.fromSpec := (Category.assoc _ _ _).symm
      _ = Scheme.Spec.map (op β) ≫ hU.fromSpec := by
          refine congrArg (fun r => r ≫ hU.fromSpec) ?_
          exact hBase (q _ _ fki.unop.le)
  have hφ' : Scheme.Spec.map (op φR) = aKV := by simpa [φR] using hφ
  have hcompatSpec : aKV ≫ Scheme.Spec.map (op α) = Scheme.Spec.map (op β) := by
    refine (cancel_mono hU.fromSpec).mp ?_
    calc
      (aKV ≫ Scheme.Spec.map (op α)) ≫ hU.fromSpec
          = aKV ≫ Scheme.Spec.map (op α) ≫ hU.fromSpec := Category.assoc _ _ _
      _ = aKV ≫ hV.fromSpec ≫ X.obj.hom := congrArg (fun r => aKV ≫ r) hfVw.symm
      _ = (aKV ≫ hV.fromSpec) ≫ X.obj.hom := (Category.assoc _ _ _).symm
      _ = aK ≫ X.obj.hom := congrArg (fun r => r ≫ X.obj.hom) haKV
      _ = Scheme.Spec.map (op β) ≫ hU.fromSpec := hKf
  have hSpecα : Spec.map α = Scheme.Spec.map (op α) := rfl
  have hSpecβ : Spec.map β = Scheme.Spec.map (op β) := rfl
  have hφSpec : Spec.map φR = aKV := hφ'
  have hcompat : α ≫ φR = β :=
    Spec.map_injective (by rw [Spec.map_comp, hφSpec, hSpecα, hSpecβ]; exact hcompatSpec)
  have hαdef : CommRingCat.ofHom (algebraMap ↑R ↑A) = α := rfl
  let σ : ↑A →ₐ[↑R] G k.unop :=
    { toRingHom := φR.hom
      commutes' := by
        intro r
        have h := congrArg (fun r' : R ⟶ CommRingCat.of (G k.unop) => r' r) hcompat
        change φR.hom (α.hom r) = β.hom r at h
        have hα' : α.hom = algebraMap ↑R ↑A := (congrArg CommRingCat.Hom.hom hαdef).symm
        rw [hα'] at h
        simpa [β] using h }
  have hproj : cZ.π.app k ≫ aKV = 𝟙 (Spec A) := by
    refine (cancel_mono hV.fromSpec).mp ?_
    calc
      (cZ.π.app k ≫ aKV) ≫ hV.fromSpec = cZ.π.app k ≫ aK := by rw [Category.assoc, haKV]
      _ = hV.fromSpec := by
          calc
            cZ.π.app k ≫ aK = (cZ.π.app k ≫ Z.map fki) ≫ aI := (Category.assoc _ _ _).symm
            _ = cZ.π.app i.unop ≫ aI := by rw [cZ.w fki]
            _ = hV.fromSpec := hmScheme
      _ = 𝟙 (Spec A) ≫ hV.fromSpec := (Category.id_comp _).symm
  have hπk : cZ.π.app k = Spec.map (CommRingCat.ofHom (g k.unop).toRingHom) := rfl
  have hretRing : φR ≫ CommRingCat.ofHom (g k.unop).toRingHom = 𝟙 A :=
    Spec.map_injective (by
      rw [Spec.map_comp, Spec.map_id, hφSpec, ← hπk]
      exact hproj)
  have hret : (g k.unop).comp σ = AlgHom.id ↑R ↑A := by
    refine AlgHom.ext fun a => ?_
    have h := congrArg (fun r : A ⟶ A => r a) hretRing
    simpa [σ, CommRingCat.hom_comp] using h
  exact Stacks.AlgebraCategory.Presentability.finitePresentation_of_retract σ (g k.unop)
    fun a => by simpa using AlgHom.congr_fun hret a

end AlgebraicGeometry.ExtendingFunctors

end

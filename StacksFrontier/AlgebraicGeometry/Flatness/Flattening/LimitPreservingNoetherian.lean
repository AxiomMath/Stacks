module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.Ring.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.LimitPreserving
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.RingTheory.Algebra.DirectLimit.FinitePresentation
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.CategoryTheory.Limits.Over
public import Mathlib.CategoryTheory.Limits.Types.Colimits

/-!
# A limit-preserving functor of points on locally Noetherian schemes (Stacks 0GE4)

Over a locally Noetherian base `S`, let `X` be an object of the chosen big site over `S` whose
underlying scheme is locally Noetherian. Following Stacks 0GE4, if the functor of points of
`X`, restricted to the locally Noetherian objects of that site, preserves directed inverse
limits of affine schemes in the sense of Stacks 049J, then `X` is locally of finite
presentation over `S`.

## Main definitions

* `AlgebraicGeometry.LocallyNoetherianOver`: the full subcategory of the chosen big site over
  `S` on the objects whose underlying scheme is locally Noetherian, with
  `AlgebraicGeometry.LocallyNoetherianOver.toScheme` its underlying-scheme functor.

## Main results

* `AlgebraicGeometry.locallyOfFinitePresentation_of_limitPreserving_yoneda`: **Stacks 0GE4**.

## Implementation notes

The topology plays no part in the statement: all five sites of the source have the same
underlying category, so the condition is stated over the chosen big fppf site. The
subcategory is cut out by *locally* Noetherian schemes, as the source stipulates at the start
of its section, and the standing hypothesis that the base is locally Noetherian is carried as
an instance argument. Limit preservation is tested on cofiltered index categories whose object
and morphism universes are both `u`, the universe of the schemes; that is what the proof needs,
since the directed system of finite-presentation approximations it builds is indexed in `u`,
and a smaller index universe need not detect finite presentation.

The proof is the source's. Working on an affine chart `V ⊆ X` over an affine chart `U ⊆ S`,
write the ring of `V` as a directed colimit of finitely presented algebras over the ring of `U`
(`Algebra.exists_directedSystem_finitePresentation_lift_bijective`); each stage is Noetherian,
hence lies in the locally Noetherian subcategory, and the whole system is small enough for the
site by `AlgebraicGeometry.Scheme.size_Spec_lt_of_finiteType`. Applying the spectrum functor turns
the colimit of rings into an inverse limit of affine schemes in the site, and limit preservation
factors the chart `V ⟶ X` through one stage. Shrinking the index once more so that the
factorisation lands inside `V`, that stage's map is a section of the colimit map, so the ring of
`V` is a retract of a finitely presented algebra and therefore finitely presented itself; the
retract step is `Stacks.AlgebraCategory.Presentability.finitePresentation_of_retract`.

| Stacks tag | library name |
|---|---|
| Tag 021R | `AlgebraicGeometry.BigFppfSite` |
| Tag 021S | `AlgebraicGeometry.BigFppfOver` |
| Tag 049J | `AlgebraicGeometry.LimitPreserving` |
| Tag 0GE4 | `AlgebraicGeometry.LocallyNoetherianOver` |

## References

* [Stacks Project, Tag 0GE4](https://stacks.math.columbia.edu/tag/0GE4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u

/-- The locally Noetherian objects of the chosen big site over `S`. -/
abbrev LocallyNoetherianOver (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :=
  ObjectProperty.FullSubcategory (fun T : BigFppfOver B S hS =>
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))

/-- The underlying-scheme functor on the locally Noetherian site over `S`. -/
abbrev LocallyNoetherianOver.toScheme (B : BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    LocallyNoetherianOver B S hS ⥤ Scheme.{u} :=
  (ObjectProperty.ι (fun T : BigFppfOver B S hS =>
    IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj T))) ⋙
      BigFppfOver.toScheme B S hS

/-- Composing the spectra of an `R`-algebra map and of the structure map gives the spectrum of the
target's structure map. -/
private lemma spec_map_algHom_comp_spec_map_algebraMap {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (φ : A →ₐ[R] B) :
    Scheme.Spec.map (Opposite.op (CommRingCat.ofHom φ.toRingHom)) ≫
      Scheme.Spec.map (Opposite.op (CommRingCat.ofHom (algebraMap R A))) =
      Scheme.Spec.map (Opposite.op (CommRingCat.ofHom (algebraMap R B))) := by
  rw [← Scheme.Spec.map_comp]
  apply congrArg Scheme.Spec.map
  apply congrArg Opposite.op
  ext r
  exact φ.commutes r

private lemma factors_through_stage_of_limitPreserving
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : LocallyNoetherianOver B S hS)
    (hX : LimitPreserving.{u, u, u, u, u + 1, u}
      (LocallyNoetherianOver.toScheme B S hS) (yoneda.obj X))
    (I : Type u) [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ LocallyNoetherianOver B S hS) (c : Cone D)
    (hc : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone c))
    (ha : ∀ i, IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)))
    (haTop : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj c.pt))
    (f : c.pt ⟶ X) : ∃ i, ∃ g : D.obj i ⟶ X, c.π.app i ≫ g = f := by
  obtain ⟨hcolim⟩ := hX I D c hc ha haTop
  obtain ⟨i, g, hg⟩ := Types.jointly_surjective_of_isColimit hcolim f
  exact ⟨i.unop, g, by simpa using hg⟩

/-- A limit-preserving representable functor on the locally Noetherian site
represents a scheme locally of finite presentation over the base. -/
@[stacks 0GE4, sga "3 XI 3.2" "partial"]
theorem locallyOfFinitePresentation_of_limitPreserving_yoneda
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    [IsLocallyNoetherian S] (hS : B.Contains S)
    (X : LocallyNoetherianOver B S hS)
    (hX : LimitPreserving.{u, u, u, u, u + 1, u}
      (LocallyNoetherianOver.toScheme B S hS) (yoneda.obj X)) :
    LocallyOfFinitePresentation (B.inclusion.map X.1.hom) := by
  let Y := (LocallyNoetherianOver.toScheme B S hS).obj X
  let f : Y ⟶ S := B.inclusion.map X.1.hom
  show LocallyOfFinitePresentation f
  have hlfp : LocallyOfFinitePresentation f := by
    rw [locallyOfFinitePresentation_iff]
    intro U hU V hV e
    let R : CommRingCat.{u} := CommRingCat.of Γ(S, U)
    let A : CommRingCat.{u} := CommRingCat.of Γ(Y, V)
    let α : R ⟶ A := f.appLE U V e
    let : Algebra ↑R ↑A := α.hom.toAlgebra
    have hRnoeth : IsNoetherianRing ↑R :=
      IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
    let : IsNoetherianRing R := hRnoeth
    obtain ⟨Λ, hpo, hnon, hdir, G, hComm, hAlg, q, hDS, g, hg, hfp, hftype, hbij⟩ :=
      Algebra.exists_directedSystem_finitePresentation_lift_bijective ↑R ↑A
    let : PartialOrder Λ := hpo
    let : Nonempty Λ := hnon
    let : IsDirectedOrder Λ := hdir
    let : ∀ l, CommRing (G l) := hComm
    let : ∀ l, Algebra ↑R (G l) := hAlg
    let : DirectedSystem G (fun i j h ↦ ⇑(q i j h)) := hDS
    have hSpecU : (Spec R).size < B.cutoff := by
      calc
        (Spec R).size = (U : Scheme).size := Scheme.size_congr hU.isoSpec.symm
        _ ≤ S.size := Scheme.size_coe_opens_le S U
        _ < B.cutoff := hS
    have hsmall (l : Λ) : (Spec (CommRingCat.of (G l))).size < B.cutoff := by
      have : Algebra.FiniteType ↑R (G l) := inferInstance
      exact Scheme.size_Spec_lt_of_finiteType B.aleph0_lt_cutoff
        B.cutoff_isStrongPrelimit ↑R (G l) hSpecU
    have hstageNoeth (l : Λ) : IsLocallyNoetherian (Spec (CommRingCat.of (G l))) := by
      have : Algebra.FiniteType ↑R (G l) := inferInstance
      have : IsNoetherianRing (G l) := Algebra.FiniteType.isNoetherianRing ↑R (G l)
      exact isLocallyNoetherian_Spec.mpr inferInstance
    have hsourceNoeth : IsLocallyNoetherian (Spec A) := by
      have : IsNoetherianRing A := X.property.component_noetherian ⟨V, hV⟩
      exact isLocallyNoetherian_Spec.mpr inferInstance
    -- Put the directed system of finitely presented algebras into the locally Noetherian site.
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
    let Z : Λᵒᵖ ⥤ Scheme.{u} := D₀.op ⋙ Scheme.Spec
    let cZ : Cone Z := Scheme.Spec.mapCone c₀.op
    have hcZ : IsLimit cZ := isLimitOfPreserves Scheme.Spec hc₀.op
    have hASmall : (Spec A).size < B.cutoff := by
      calc
        (Spec A).size = (V : Scheme).size := Scheme.size_congr hV.isoSpec.symm
        _ ≤ Y.size := Scheme.size_coe_opens_le Y V
        _ < B.cutoff := X.1.left.property
    let ZB : Λᵒᵖ ⥤ B.Schemes :=
      { obj i := B.obj (hsmall i.unop)
        map {i j} m := ⟨Z.map m⟩
        map_id i := B.inclusion.map_injective (Z.map_id i)
        map_comp f g := by
          apply B.inclusion.map_injective
          simp [Z] }
    let cB : Cone ZB :=
      { pt := B.obj hASmall
        π :=
          { app i := ObjectProperty.homMk (cZ.π.app i)
            naturality i j m := ObjectProperty.hom_ext _ (cZ.w m).symm } }
    let s : ZB ⟶ (Functor.const Λᵒᵖ).obj (B.obj hS) :=
      { app i := ObjectProperty.homMk (Scheme.Spec.map (Opposite.op (CommRingCat.ofHom
          (algebraMap ↑R (G i.unop)))) ≫ hU.fromSpec)
        naturality := by
          intro i j m
          apply B.inclusion.map_injective
          dsimp [ZB, Z]
          simp only [Category.comp_id]
          exact congrArg (fun a => a ≫ hU.fromSpec)
            (spec_map_algHom_comp_spec_map_algebraMap (q _ _ m.unop.le)) }
    let p : B.obj hASmall ⟶ B.obj hS :=
      ObjectProperty.homMk (Scheme.Spec.map (Opposite.op α) ≫ hU.fromSpec)
    have hp (i : Λᵒᵖ) : cB.π.app i ≫ s.app i = p := by
      apply B.inclusion.map_injective
      dsimp [cB, s, p, ZB, cZ, Z]
      exact congrArg (fun a => a ≫ hU.fromSpec)
        (spec_map_algHom_comp_spec_map_algebraMap (g i.unop))
    let cOver := Over.liftCone ZB s cB p hp
    let E := LocallyNoetherianOver B S hS
    let DOver := Over.lift ZB s
    let D : Λᵒᵖ ⥤ E :=
      { obj i := ⟨DOver.obj i, hstageNoeth i.unop⟩
        map f := ObjectProperty.homMk (DOver.map f)
        map_id i := ObjectProperty.hom_ext _ (DOver.map_id i)
        map_comp f g := ObjectProperty.hom_ext _ (DOver.map_comp f g) }
    let c : Cone D :=
      { pt := ⟨cOver.pt, hsourceNoeth⟩
        π :=
          { app i := ObjectProperty.homMk (cOver.π.app i)
            naturality i j f := ObjectProperty.hom_ext _ (cOver.w f).symm } }
    have hc : IsLimit ((LocallyNoetherianOver.toScheme B S hS).mapCone c) := hcZ
    have ha (i : Λᵒᵖ) : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj (D.obj i)) := by
      show IsAffine (Spec (CommRingCat.of (G i.unop)))
      infer_instance
    have hAffineZ (i : Λᵒᵖ) : IsAffine (Z.obj i) := by
      show IsAffine (Spec (CommRingCat.of (G i.unop)))
      infer_instance
    let {i j : Λᵒᵖ} (gij : i ⟶ j) : IsAffineHom (Z.map gij) := by
      have hi := hAffineZ i
      have hj := hAffineZ j
      infer_instance
    have htop : IsAffine ((LocallyNoetherianOver.toScheme B S hS).obj c.pt) := by
      show IsAffine (Spec (CommRingCat.of A))
      infer_instance
    have hBaseChart : hV.fromSpec ≫ f =
        Scheme.Spec.map (Opposite.op α) ≫ hU.fromSpec := by
      simpa using (IsAffineOpen.SpecMap_appLE_fromSpec f hU hV e).symm
    let fV : c.pt ⟶ X := ObjectProperty.homMk <|
      Over.homMk (ObjectProperty.homMk hV.fromSpec) (B.inclusion.map_injective hBaseChart)
    obtain ⟨i, m, hm⟩ := factors_through_stage_of_limitPreserving B S hS X hX
      (Λᵒᵖ) D c hc ha htop fV
    let F := LocallyNoetherianOver.toScheme B S hS
    let aI : Z.obj i ⟶ Y := F.map m
    have hmScheme : cZ.π.app i ≫ aI = hV.fromSpec :=
      (F.map_comp _ _).symm.trans (congrArg F.map hm)
    have hpre : (cZ.π.app i) ⁻¹ᵁ (aI ⁻¹ᵁ V) = ⊤ := by
      show (cZ.π.app i ≫ aI) ⁻¹ᵁ V = ⊤
      rw [hmScheme]
      exact hV.fromSpec_preimage_self
    obtain ⟨k, fki, hkV⟩ := exists_map_eq_top Z cZ hcZ (aI ⁻¹ᵁ V) hpre (i := i)
    let aK : Z.obj k ⟶ Y := Z.map fki ≫ aI
    have haK : aK ⁻¹ᵁ V = ⊤ := hkV
    have hrange : Set.range aK ⊆ Set.range hV.fromSpec := by
      rw [hV.range_fromSpec, Set.range_subset_iff]
      show ∀ x : Z.obj k, (aK x : Y) ∈ (V : Set Y)
      intro x
      have hx : x ∈ aK ⁻¹ᵁ V := by rw [haK]; trivial
      exact (Scheme.Hom.mem_preimage aK).mp hx
    let aKV : Z.obj k ⟶ Spec A := IsOpenImmersion.lift hV.fromSpec aK hrange
    have haKV : aKV ≫ hV.fromSpec = aK := IsOpenImmersion.lift_fac _ _ _
    obtain ⟨φ, hφ⟩ := Scheme.Spec.map_surjective aKV
    let φR : A ⟶ CommRingCat.of (G k.unop) := φ.unop
    let β : R ⟶ CommRingCat.of (G k.unop) :=
      CommRingCat.ofHom (algebraMap ↑R (G k.unop))
    have hKf : aK ≫ f =
        Scheme.Spec.map (Opposite.op β) ≫ hU.fromSpec := by
      have hIf : aI ≫ f =
          Scheme.Spec.map (Opposite.op (CommRingCat.ofHom
            (algebraMap ↑R (G i.unop)))) ≫ hU.fromSpec :=
        congrArg (fun q => B.inclusion.map q) (Over.w m.1)
      calc
        aK ≫ f = (Z.map fki ≫ Scheme.Spec.map (Opposite.op (CommRingCat.ofHom
            (algebraMap ↑R (G i.unop))))) ≫ hU.fromSpec := by
          simp only [aK, Category.assoc, hIf]
        _ = Scheme.Spec.map (Opposite.op β) ≫ hU.fromSpec := by
          congr 1
          exact spec_map_algHom_comp_spec_map_algebraMap (q _ _ fki.unop.le)
    have hφ' : Scheme.Spec.map (Opposite.op φR) = aKV := by
      simpa [φR] using hφ
    have hcompatSpec : aKV ≫ Scheme.Spec.map (Opposite.op α) =
        Scheme.Spec.map (Opposite.op β) := by
      apply (cancel_mono hU.fromSpec).mp
      rw [Category.assoc, ← hBaseChart, ← Category.assoc, haKV, hKf]
    have hcompat : α ≫ φR = β := by
      have hOpp : Opposite.op (α ≫ φR) = Opposite.op β := by
        apply Scheme.Spec.map_injective
        show Scheme.Spec.map (Opposite.op φR ≫ Opposite.op α) = _
        rw [Functor.map_comp, hφ']
        exact hcompatSpec
      exact congrArg Opposite.unop hOpp
    let σ : ↑A →ₐ[↑R] G k.unop :=
      { toRingHom := φR.hom
        commutes' := by
          intro r
          have h := congrArg (fun q : R ⟶ CommRingCat.of (G k.unop) => q r) hcompat
          change φR.hom (algebraMap ↑R ↑A r) = β.hom r at h
          simpa [β] using h }
    have hproj : cZ.π.app k ≫ aKV = 𝟙 (Spec A) := by
      apply (cancel_mono hV.fromSpec).mp
      rw [Category.assoc, haKV]
      simp only [aK, ← hmScheme, ← cZ.w fki, Category.assoc]
      exact (Category.id_comp _).symm
    have hπ : cZ.π.app k = Scheme.Spec.map (Opposite.op
        (CommRingCat.ofHom (g k.unop).toRingHom)) := by
      dsimp [cZ, Z, c₀, D₀]
    have hmapid : Scheme.Spec.map (Opposite.op (𝟙 A)) = 𝟙 (Spec A) := by
      show Scheme.Spec.map (𝟙 (Opposite.op A)) = _
      exact Scheme.Spec.map_id (Opposite.op A)
    have hretRing : φR ≫ CommRingCat.ofHom (g k.unop).toRingHom = 𝟙 A := by
      have hOpp : Opposite.op
          (φR ≫ CommRingCat.ofHom (g k.unop).toRingHom) = Opposite.op (𝟙 A) := by
        apply Scheme.Spec.map_injective
        show Scheme.Spec.map (Opposite.op (CommRingCat.ofHom (g k.unop).toRingHom) ≫
          Opposite.op φR) = _
        rw [Functor.map_comp, ← hπ, hφ', hmapid]
        exact hproj
      exact congrArg Opposite.unop hOpp
    have hret : (g k.unop).comp σ = AlgHom.id ↑R ↑A := by
      apply AlgHom.ext
      intro a
      have h := congrArg (fun q : A ⟶ A => q a) hretRing
      simpa [σ, CommRingCat.hom_comp] using h
    exact Stacks.AlgebraCategory.Presentability.finitePresentation_of_retract σ (g k.unop)
      (fun a => by simpa using AlgHom.congr_fun hret a)
  exact hlfp

end AlgebraicGeometry

end

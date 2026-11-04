module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Stalk
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Gluing.Punctured
public import StacksFrontier.AlgebraicGeometry.StalkAffineNhdsLimit.Basic

/-!
# Gluing a morphism from its restriction off a closed point and its germ there

Let `X` and `Y` be schemes over `S` with `Y` locally of finite presentation over `S`, and let
`x` be a closed point of `X` whose open complement `U = X \ {x}` has quasi-compact inclusion.
A morphism `X ⟶ Y` over `S` is determined by, and can be built from, a pair: a morphism
`U ⟶ Y` over `S` and a morphism `Spec 𝒪_{X,x} ⟶ Y` over `S` which agree on
`V = Spec 𝒪_{X,x} \ {x}`.

## Main results

* `AlgebraicGeometry.existsUnique_hom_of_punctured_and_stalk`: a morphism `X ⟶ Y` over `S` is
  glued uniquely from a morphism on `U` and a morphism on `Spec 𝒪_{X,x}` agreeing on `V`.

## Implementation notes

The bijection of the source is stated as a unique-existence: given the pair and their agreement
over `V`, there is exactly one morphism `X ⟶ Y` over `S` restricting to each. Agreement over `V`
is expressed by equality of the two composites out of the fibre product of `U.ι` with
`X.fromSpecStalk x`.

`Spec 𝒪_{X,x}` is the limit of the affine open neighbourhoods of `x`
(`AlgebraicGeometry.isLimitSpecStalkCone`), and the preimage in it of an open of `X` is the limit
of the preimages (`AlgebraicGeometry.isLimitOpensSpecStalkCone`), both indexed by
`AlgebraicGeometry.AffineOpenNhds`. Local finite presentation of `Y ⟶ S` then lets Stacks 01ZC
descend the germ `b` to a morphism from some affine neighbourhood `W` of `x`, uniquely up to
shrinking `W`. Quasi-compactness of `U ⟶ X` makes each `U ∩ W` quasi-compact
(`AlgebraicGeometry.isCompact_inter_of_quasiCompact_ι`), so `V` is a limit of quasi-compact
quasi-separated schemes and the same descent identifies `a` and the descended germ over `U ∩ W`
after shrinking. Gluing `a` and that morphism along `U ∩ W` gives the morphism on `X`.

## References

* [The Stacks Project, Lemma 32.6.5 (0GWT)](https://stacks.math.columbia.edu/tag/0GWT)
* [The Stacks Project, Proposition 32.6.1 (01ZC)](https://stacks.math.columbia.edu/tag/01ZC)
* [The Stacks Project, Lemma 32.4.5 (01YX)](https://stacks.math.columbia.edu/tag/01YX)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The open immersions of the affine open neighbourhoods of `x` into `X`, as a natural
transformation from `AlgebraicGeometry.affineOpenNhdsDiagram` to the constant diagram `X`. -/
private noncomputable def affineOpenNhdsDiagramToSelf (X : Scheme.{u}) (x : X) :
    affineOpenNhdsDiagram X x ⟶ (Functor.const (AffineOpenNhds X x)).obj X where
  app W := Scheme.Opens.ι (X := X) W.obj.1
  naturality _ _ _ := by simp

private lemma exists_local_extension
    {S X Y : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    [LocallyOfFinitePresentation fY] (x : X)
    (b : Spec (X.presheaf.stalk x) ⟶ Y)
    (hb : b ≫ fY = X.fromSpecStalk x ≫ fX) :
    ∃ (W : X.Opens) (hxW : x ∈ W) (c : W.toScheme ⟶ Y),
      c ≫ fY = W.ι ≫ fX ∧ W.fromSpecStalkOfMem x hxW ≫ c = b := by
  let δ := affineOpenNhdsDiagramToSelf X x
  have hbase : (specStalkCone X x).π ≫ (δ ≫ (Functor.const (AffineOpenNhds X x)).map fX) =
      (Functor.const _).map (b ≫ fY) := by
    ext W
    show Scheme.Opens.fromSpecStalkOfMem (X := X) W.obj.1 x W.obj.2 ≫
      Scheme.Opens.ι (X := X) W.obj.1 ≫ fX = b ≫ fY
    rw [← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, hb]
  obtain ⟨W, g, hg, hgf⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    (affineOpenNhdsDiagram X x) (δ ≫ (Functor.const (AffineOpenNhds X x)).map fX) fY
    (specStalkCone X x) (isLimitSpecStalkCone X x) b hbase
  exact ⟨W.obj.1, W.obj.2, g, hgf, hg⟩

private lemma exists_hom_of_covering_opens
    {X Y : Scheme.{u}} (U V : X.Opens) (hcover : U ⊔ V = ⊤)
    (a : U.toScheme ⟶ Y) (b : V.toScheme ⟶ Y)
    (hab : pullback.fst U.ι V.ι ≫ a = pullback.snd U.ι V.ι ≫ b) :
    ∃ f : X ⟶ Y, U.ι ≫ f = a ∧ V.ι ≫ f = b := by
  let opens : Bool → X.Opens := fun i => if i then V else U
  have hopen : TopologicalSpace.IsOpenCover opens := by
    show (⨆ i, opens i) = ⊤
    simpa [opens, iSup_bool_eq, sup_comm] using hcover
  let cover := X.openCoverOfIsOpenCover opens hopen
  let maps : ∀ i : Bool, (opens i).toScheme ⟶ Y := fun i =>
    match i with
    | false => a
    | true => b
  have hmaps : ∀ i j, pullback.fst (cover.f i) (cover.f j) ≫ maps i =
      pullback.snd (cover.f i) (cover.f j) ≫ maps j := by
    intro i j
    cases i <;> cases j
    · have h : pullback.fst U.ι U.ι = pullback.snd U.ι U.ι :=
        (cancel_mono U.ι).mp pullback.condition
      exact congrArg (fun g => g ≫ a) h
    · exact hab
    · show pullback.fst V.ι U.ι ≫ b = pullback.snd V.ι U.ι ≫ a
      have h := congrArg (fun g => (pullbackSymmetry V.ι U.ι).hom ≫ g) hab.symm
      rw [← Category.assoc, ← Category.assoc,
        pullbackSymmetry_hom_comp_snd, pullbackSymmetry_hom_comp_fst] at h
      exact h
    · have h : pullback.fst V.ι V.ι = pullback.snd V.ι V.ι :=
        (cancel_mono V.ι).mp pullback.condition
      exact congrArg (fun g => g ≫ b) h
  exact ⟨cover.glueMorphisms maps hmaps,
    cover.ι_glueMorphisms maps hmaps false, cover.ι_glueMorphisms maps hmaps true⟩

/-- Morphisms from a scheme are glued uniquely from its punctured complement and the local
scheme at a closed point, when the target is locally of finite presentation over the base. -/
@[stacks 0GWT]
theorem existsUnique_hom_of_punctured_and_stalk
    {S X Y : Scheme.{u}} (fX : X ⟶ S) (fY : Y ⟶ S)
    [LocallyOfFinitePresentation fY] (x : X) (hx : IsClosed ({x} : Set X)) :
    let U : X.Opens := ⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩
    ∀ (_hU : QuasiCompact U.ι)
      (a : U.toScheme ⟶ Y) (b : Spec (X.presheaf.stalk x) ⟶ Y),
      a ≫ fY = U.ι ≫ fX →
      b ≫ fY = X.fromSpecStalk x ≫ fX →
      pullback.fst U.ι (X.fromSpecStalk x) ≫ a =
        pullback.snd U.ι (X.fromSpecStalk x) ≫ b →
      ∃! f : X ⟶ Y,
        (f ≫ fY = fX) ∧ (U.ι ≫ f = a) ∧ (X.fromSpecStalk x ≫ f = b) := by
  classical
  dsimp
  let U : X.Opens := ⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩
  intro hU a b ha hb hab
  obtain ⟨W, hxW, cW, hcW, hcbW⟩ := exists_local_extension fX fY x b hb
  obtain ⟨A, hA, hxA, hAW⟩ := exists_isAffineOpen_mem_and_subset hxW
  let initial : AffineOpenNhds X x := ⟨⟨A, hxA⟩, hA⟩
  let D := affineOpenNhdsDiagram X x
  let δ := affineOpenNhdsDiagramToSelf X x
  let cD := specStalkCone X x
  have : ∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g) := fun _ => inferInstance
  have : ∀ i, CompactSpace (D.obj i) := fun _ => inferInstance
  have : ∀ i, QuasiSeparatedSpace (D.obj i) := fun _ => inferInstance
  let ιA : D.obj initial ⟶ X := Scheme.Opens.ι (X := X) A
  let πA : Spec (X.presheaf.stalk x) ⟶ D.obj initial := cD.π.app initial
  let cA : D.obj initial ⟶ Y := X.homOfLE hAW ≫ cW
  have hcA : cA ≫ fY = ιA ≫ fX := by
    show (X.homOfLE hAW ≫ cW) ≫ fY = Scheme.Opens.ι (X := X) A ≫ fX
    rw [Category.assoc, hcW, ← Category.assoc]
    congr 1
    exact Scheme.homOfLE_ι X hAW
  have hmapA : A.fromSpecStalkOfMem x hxA ≫ X.homOfLE hAW =
      W.fromSpecStalkOfMem x hxW := by
    apply (cancel_mono W.ι).mp
    rw [Category.assoc]
    refine Eq.trans ?_ ((Scheme.Opens.fromSpecStalkOfMem_ι W x hxW).symm)
    refine Eq.trans ?_ (Scheme.Opens.fromSpecStalkOfMem_ι A x hxA)
    congr 1
    exact Scheme.homOfLE_ι X hAW
  have hcbA : πA ≫ cA = b := by
    show A.fromSpecStalkOfMem x hxA ≫ (X.homOfLE hAW ≫ cW) = b
    rw [← Category.assoc, hmapA, hcbW]
  have hlimX : πA ≫ ιA = X.fromSpecStalk x :=
    Scheme.Opens.fromSpecStalkOfMem_ι A x hxA
  let V : (D.obj initial).Opens := ιA ⁻¹ᵁ U
  let E := opensDiagram D initial V
  let cE := opensCone D cD initial V
  have hcE : IsLimit cE := isLimitOpensSpecStalkCone X x initial U
  have hVcompact : IsCompact (V : Set (D.obj initial)) :=
    isCompact_inter_of_quasiCompact_ι U A hU hA.isCompact
  have : ∀ j : Over initial, CompactSpace (E.obj j) :=
    compactSpace_opensDiagram_obj_of_isCompact D initial V hVcompact
  have : ∀ j : Over initial, QuasiSeparatedSpace (E.obj j) :=
    quasiSeparatedSpace_opensDiagram_obj D initial V
  let tX : E ⟶ (Functor.const (Over initial)).obj X :=
    opensDiagramι D initial V ≫ Functor.whiskerLeft (Over.forget initial) δ
  let t := tX ≫ (Functor.const (Over initial)).map fX
  let first : Over initial := Over.mk (𝟙 initial)
  let q : E.obj first ⟶ D.obj initial := (opensDiagramι D initial V).app first
  have hqU : Set.range (q ≫ ιA) ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨(q ≫ ιA) z, ?_⟩, rfl⟩
    show ιA z.val ∈ U
    have hz : q z ∈ D.map (𝟙 initial) ⁻¹ᵁ V := z.2
    rw [CategoryTheory.Functor.map_id, Scheme.Hom.id_preimage] at hz
    exact hz
  let aFirst : E.obj first ⟶ U.toScheme := IsOpenImmersion.lift U.ι (q ≫ ιA) hqU
  have haFirst : aFirst ≫ U.ι = q ≫ ιA := IsOpenImmersion.lift_fac _ _ _
  let localA : E.obj first ⟶ Y := aFirst ≫ a
  let localB : E.obj first ⟶ Y := q ≫ cA
  have haBase : t.app first = localA ≫ fY := by
    show q ≫ ιA ≫ fX = (aFirst ≫ a) ≫ fY
    rw [Category.assoc, ha, ← Category.assoc aFirst, haFirst, Category.assoc]
  have hbBase : t.app first = localB ≫ fY := by
    show q ≫ ιA ≫ fX = (q ≫ cA) ≫ fY
    rw [Category.assoc, hcA]
  let L : (Spec (X.presheaf.stalk x)).Opens := πA ⁻¹ᵁ V
  have hL : L = X.fromSpecStalk x ⁻¹ᵁ U := specStalkCone_π_preimage X x initial U
  let πE : L.toScheme ⟶ E.obj first := cE.π.app first
  have hprojection : πE ≫ q = L.ι ≫ πA := Scheme.Hom.resLE_comp_ι _ _
  have hrange : Set.range (L.ι ≫ X.fromSpecStalk x) ⊆ Set.range U.ι := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨(L.ι ≫ X.fromSpecStalk x) z, ?_⟩, rfl⟩
    show (X.fromSpecStalk x) (L.ι z) ∈ U
    exact (show L ≤ X.fromSpecStalk x ⁻¹ᵁ U from hL.le) z.2
  let toU : L.toScheme ⟶ U.toScheme :=
    IsOpenImmersion.lift U.ι (L.ι ≫ X.fromSpecStalk x) hrange
  have htoU : toU ≫ U.ι = L.ι ≫ X.fromSpecStalk x :=
    IsOpenImmersion.lift_fac _ _ _
  let toOverlap : L.toScheme ⟶ pullback U.ι (X.fromSpecStalk x) :=
    pullback.lift toU L.ι htoU
  have hlimitA : πE ≫ aFirst = toU := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, haFirst, ← Category.assoc, hprojection, Category.assoc, hlimX]
    exact htoU.symm
  have hlimitB : πE ≫ localB = L.ι ≫ b := by
    show πE ≫ (q ≫ cA) = L.ι ≫ b
    rw [← Category.assoc, hprojection, Category.assoc]
    exact congrArg (fun g => L.ι ≫ g) hcbA
  have hlimit : πE ≫ localA = πE ≫ localB := by
    calc
      πE ≫ localA = toU ≫ a := by
        rw [show localA = aFirst ≫ a from rfl, ← Category.assoc, hlimitA]
      _ = L.ι ≫ b := by
        have h := congrArg (fun g => toOverlap ≫ g) hab
        rw [← Category.assoc, ← Category.assoc,
          pullback.lift_fst, pullback.lift_snd] at h
        exact h
      _ = πE ≫ localB := hlimitB.symm
  obtain ⟨index, transition, heq⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    E t fY cE hcE localA localB haBase hbBase hlimit
  let B : X.Opens := index.left.obj.1
  let ιB : D.obj index.left ⟶ X := Scheme.Opens.ι (X := X) B
  let πB : Spec (X.presheaf.stalk x) ⟶ D.obj index.left := cD.π.app index.left
  let cB : D.obj index.left ⟶ Y := D.map index.hom ≫ cA
  let inclusion : E.obj index ⟶ D.obj index.left := (opensDiagramι D initial V).app index
  have : IsOpenImmersion inclusion :=
    inferInstanceAs (IsOpenImmersion ((opensDiagramι D initial V).app index))
  have htransition : E.map transition ≫ q = inclusion ≫ D.map index.hom := by
    have hleft : transition.left = index.hom :=
      (Category.comp_id transition.left).symm.trans (Over.w transition)
    have h := (opensDiagramι D initial V).naturality transition
    change E.map transition ≫ q = inclusion ≫ D.map transition.left at h
    rw [hleft] at h
    exact h
  have hBι : D.map index.hom ≫ ιA = ιB :=
    (δ.naturality index.hom).trans (Category.comp_id _)
  have hcB : cB ≫ fY = ιB ≫ fX := by
    show (D.map index.hom ≫ cA) ≫ fY = ιB ≫ fX
    rw [Category.assoc, hcA, ← Category.assoc, hBι]
  have hcbB : πB ≫ cB = b := by
    show πB ≫ (D.map index.hom ≫ cA) = b
    rw [← Category.assoc, show πB ≫ D.map index.hom = πA from cD.w index.hom]
    exact hcbA
  have hπB : πB ≫ ιB = X.fromSpecStalk x :=
    Scheme.Opens.fromSpecStalkOfMem_ι B x index.left.obj.2
  have hoverlap : (D.map index.hom ⁻¹ᵁ V) = ιB ⁻¹ᵁ U := by
    show D.map index.hom ⁻¹ᵁ (ιA ⁻¹ᵁ U) = ιB ⁻¹ᵁ U
    rw [← Scheme.Hom.comp_preimage, hBι]
  let projection : pullback U.ι ιB ⟶ D.obj index.left := pullback.snd U.ι ιB
  have hprojectionRange : Set.range projection ⊆ Set.range inclusion := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨projection z, ?_⟩, rfl⟩
    show projection z ∈ D.map index.hom ⁻¹ᵁ V
    rw [hoverlap]
    show ιB (projection z) ∈ U
    have hpoint := congrArg (fun g => g z) (pullback.condition (f := U.ι) (g := ιB))
    change U.ι ((pullback.fst U.ι ιB) z) = ιB (projection z) at hpoint
    rw [← hpoint]
    exact ((pullback.fst U.ι ιB) z).2
  let toIndex : pullback U.ι ιB ⟶ E.obj index :=
    IsOpenImmersion.lift inclusion projection hprojectionRange
  have htoIndex : toIndex ≫ inclusion = projection := IsOpenImmersion.lift_fac _ _ _
  have hleft : toIndex ≫ E.map transition ≫ aFirst = pullback.fst U.ι ιB := by
    apply (cancel_mono U.ι).mp
    simp only [Category.assoc, haFirst]
    rw [← Category.assoc (E.map transition), htransition, Category.assoc, hBι,
      ← Category.assoc, htoIndex]
    exact pullback.condition.symm
  have hright : toIndex ≫ E.map transition ≫ localB = projection ≫ cB := by
    show toIndex ≫ E.map transition ≫ (q ≫ cA) = projection ≫ cB
    rw [← Category.assoc (E.map transition), htransition]
    simp only [Category.assoc]
    rw [← Category.assoc toIndex inclusion, htoIndex]
  have hcompat : pullback.fst U.ι ιB ≫ a = pullback.snd U.ι ιB ≫ cB := by
    calc
      pullback.fst U.ι ιB ≫ a = toIndex ≫ E.map transition ≫ localA := by
        show pullback.fst U.ι ιB ≫ a = toIndex ≫ E.map transition ≫ aFirst ≫ a
        rw [← Category.assoc (E.map transition), ← Category.assoc toIndex, hleft]
      _ = toIndex ≫ E.map transition ≫ localB := congrArg (fun g => toIndex ≫ g) heq
      _ = pullback.snd U.ι ιB ≫ cB := hright
  have hcover : U ⊔ B = ⊤ := by
    apply top_unique
    intro z _
    show z ∈ U ∨ z ∈ B
    by_cases hzx : z = x
    · exact Or.inr (hzx ▸ index.left.obj.2)
    · exact Or.inl hzx
  obtain ⟨f, hfU, hfB⟩ := exists_hom_of_covering_opens U B hcover a cB hcompat
  have hfB' : ιB ≫ f = cB := hfB
  have hfS : f ≫ fY = fX := by
    apply Scheme.hom_ext_of_forall
    intro z
    by_cases hzx : z = x
    · refine ⟨B, hzx ▸ index.left.obj.2, ?_⟩
      show ιB ≫ f ≫ fY = ιB ≫ fX
      rw [← Category.assoc, hfB', hcB]
    · refine ⟨U, hzx, ?_⟩
      rw [← Category.assoc, hfU, ha]
  have hfb : X.fromSpecStalk x ≫ f = b := by
    rw [← hπB, Category.assoc, hfB', hcbB]
  refine ⟨f, ⟨hfS, hfU, hfb⟩, ?_⟩
  intro g hg
  obtain ⟨smaller, restriction, hequal⟩ :=
    Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType D
      (δ ≫ (Functor.const (AffineOpenNhds X x)).map fX) fY cD
      (isLimitSpecStalkCone X x) (i := initial) (ιA ≫ g) (ιA ≫ f)
      (by show ιA ≫ fX = (ιA ≫ g) ≫ fY; rw [Category.assoc, hg.1])
      (by show ιA ≫ fX = (ιA ≫ f) ≫ fY; rw [Category.assoc, hfS])
      (by
        show πA ≫ ιA ≫ g = πA ≫ ιA ≫ f
        rw [← Category.assoc, ← Category.assoc, hlimX, hg.2.2, hfb])
  let ιS : D.obj smaller ⟶ X := Scheme.Opens.ι (X := X) smaller.obj.1
  have hι : D.map restriction ≫ ιA = ιS :=
    (δ.naturality restriction).trans (Category.comp_id _)
  have hsmall : ιS ≫ g = ιS ≫ f := by
    rw [← hι, Category.assoc, Category.assoc, hequal]
  apply Scheme.hom_ext_of_forall
  intro z
  by_cases hzx : z = x
  · exact ⟨smaller.obj.1, hzx ▸ smaller.obj.2, hsmall⟩
  · exact ⟨U, hzx, hg.2.1.trans hfU.symm⟩

end AlgebraicGeometry

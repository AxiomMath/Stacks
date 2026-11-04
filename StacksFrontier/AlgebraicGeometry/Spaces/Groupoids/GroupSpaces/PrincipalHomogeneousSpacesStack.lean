module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.PrincipalHomogeneousSpacesFibred
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorsForChangeGroup
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary

/-!
# The stack of principal homogeneous spaces, from descent of principal homogeneous spaces

Let `B` be an algebraic space over a scheme `S` and let `G` be a group algebraic space over `B`.
Stacks 04UP is a remark: it *conjectures* that, up to a replacement as in Stacks 03ZZ, the functor
`p : G-Principal ⥤ (Sch/S)_fppf` of Stacks 04UN defines a stack in groupoids, and says that this
would follow if one could show that principal homogeneous spaces satisfy effective descent along
the coverings of `(Sch/S)_fppf` (items (1)–(4) of the remark). It adds that the technique of the
proof of Stacks 04U1 reduces that descent statement to a set theoretical question, and leaves it
open.

The library does not settle the descent statement either. The technique of Stacks 04U1 glues the
`Xᵢ` to a sheaf `X` on `(Sch/U)_fppf` and then needs a single atlas of the disjoint union of the
`Xᵢ` inside the big fppf site to apply Stacks 04SK. For an fppf torsor every `Xᵢ` is fppf locally
the group, and its atlases are bounded by those of the group and of the covering; for a principal
homogeneous space, trivialized only after an fpqc covering, no such bound is available, and the
size cutoff of `AlgebraicGeometry.BigFppfSite` is a strong limit cardinal of uncountable
cofinality but need not be regular, so unboundedly many atlases below it need not fit inside the
site. That is the set theoretical question of the remark.

What the remark asserts as mathematics is therefore the implication "effective descent of
principal homogeneous spaces as in (1)–(4) implies that `p` is a stack in groupoids". The
descent statement is the Prop `AlgebraicGeometry.Space.PrincipalHomogeneousSpaceDescent`, the
antecedent of the remark's own conditional, and the implication is proved in full, under no other
assumption, as `AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.isStackInGroupoids_of_descent`.

## Main definitions

* `AlgebraicGeometry.Space.PrincipalHomogeneousSpaceDescent`: items (1)–(4) of Stacks 04UP.
* `AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.descentDatumOfBase`: a descent datum of
  `G-Principal` whose sections of `B` factor through `b : U ⟶ B`, read as a descent datum of
  principal homogeneous spaces under `U ×_{b, B} G`.

## Main results

* `AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.exists_glued_sec`: the sections of `B` of a
  descent datum of `G-Principal` glue.
* `PrincipalHomogeneousSpaces.isEffective_of_isEffective_descentDatumOfBase`: effectivity of the
  datum read under `U ×_{b, B} G` gives effectivity of the original datum.
* `AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.isStackInGroupoids_of_descent`:
  **Stacks 04UP**.

## Implementation notes

An object of `G-Principal` and the corresponding principal homogeneous space under
`U ×_{b, B} G` have the same base, the same total space and morphisms with the same underlying
pair of maps (`AlgebraicGeometry.Space.TorsorsFor.ofBase` and
`AlgebraicGeometry.Space.TorsorsFor.toBase`); so every identity between morphisms needed to move
a descent datum and its effectivity across is checked on those two maps by
`AlgebraicGeometry.Space.TorsorsFor.Hom.ext`, and every canonical comparison of restrictions is
identified by its universal property (`AlgebraicGeometry.Space.TorsorsFor.eq_compTo_of`).

## References

* [Stacks Project, Tag 04UP](https://stacks.math.columbia.edu/tag/04UP)
* [Stacks Project, Tag 04UN](https://stacks.math.columbia.edu/tag/04UN)
* [Stacks Project, Tag 04U1](https://stacks.math.columbia.edu/tag/04U1)
* [Stacks Project, Tag 04SK](https://stacks.math.columbia.edu/tag/04SK)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 03ZZ](https://stacks.math.columbia.edu/tag/03ZZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped MonoidalCategory MonObj

universe w u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}
  {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
  {G : GroupAlgebraicSpace 𝒞 S hS B hB} {P : CoveringPredicate 𝒞 S hS}

namespace TorsorsFor

/-! ### Lifts, restrictions and comparisons read off the morphism of bases -/

/-- The morphism of bases of a composite of morphisms of torsors is the composite of their
morphisms of bases. -/
@[simp]
theorem Hom.base_comp {T₁ T₂ T₃ : TorsorsFor hB G P} (φ : T₁ ⟶ T₂) (ψ : T₂ ⟶ T₃) :
    Hom.base (φ ≫ ψ) = Hom.base φ ≫ Hom.base ψ :=
  rfl

/-- The map of total spaces of a composite of morphisms of torsors is the composite of their maps
of total spaces. -/
@[simp]
theorem Hom.map_comp {T₁ T₂ T₃ : TorsorsFor hB G P} (φ : T₁ ⟶ T₂) (ψ : T₂ ⟶ T₃) :
    Hom.map (φ ≫ ψ) = Hom.map φ ≫ Hom.map ψ :=
  rfl

/-- A morphism of torsors lies over a morphism of the site as soon as its morphism of bases is
that morphism, read over prescribed objects. -/
theorem isHomLift_of_base_eq {T T' : TorsorsFor hB G P} (φ : T ⟶ T')
    {R R' : BigFppfOver 𝒞 S hS} (f : R ⟶ R') (ha : T.base = R) (hb : T'.base = R')
    (h : Hom.base φ = eqToHom ha ≫ f ≫ eqToHom hb.symm) :
    (projection hB G P).IsHomLift f φ :=
  IsHomLift.of_fac' _ f φ ha hb h

variable (hB G P) in
/-- A restriction of a torsor along a morphism `g` of the site, given by a morphism of torsors
whose morphism of bases is `g`; it is strongly cartesian because the category is fibred in
groupoids. -/
def restrictionOfBase (hp : (projection hB G P).IsFiberedInGroupoids)
    {V W : BigFppfOver 𝒞 S hS} (g : W ⟶ V) {x : TorsorsFor hB G P}
    (hx : (projection hB G P).obj x = V) (pt : TorsorsFor hB G P)
    (hpt : (projection hB G P).obj pt = W) (hom : pt ⟶ x)
    (h : Hom.base hom = eqToHom hpt ≫ g ≫ eqToHom hx.symm) :
    Functor.Restriction (projection hB G P) g x hx where
  pt := pt
  hpt := hpt
  hom := hom
  isHomLift := IsHomLift.of_fac' _ _ hom rfl rfl (by
    rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]; exact h)
  isCart := by
    have hc := hp.isStronglyCartesian hom
    have hm : (projection hB G P).map hom = eqToHom hpt ≫ g ≫ eqToHom hx.symm := h
    rwa [hm] at hc

/-- The canonical comparison of two restrictions of a torsor is the morphism over the relating
morphism of the site whose morphism of total spaces factors the one through the other. -/
theorem eq_compTo_of {U V W : BigFppfOver 𝒞 S hS} {x : TorsorsFor hB G P}
    {hx : (projection hB G P).obj x = U} (g : W ⟶ V) (f : V ⟶ U) {l : W ⟶ U}
    (hl : l = g ≫ f) (r : Functor.Restriction (projection hB G P) f x hx)
    (s : Functor.Restriction (projection hB G P) l x hx) (ψ : s.pt ⟶ r.pt)
    (hb : Hom.base ψ = eqToHom s.hpt ≫ g ≫ eqToHom r.hpt.symm)
    (hm : Hom.map ψ ≫ Hom.map r.hom = Hom.map s.hom) :
    ψ = Functor.Restriction.compTo (projection hB G P) g f hl r s := by
  subst hl
  have hr : r.pt.base = V := r.hpt
  have hs : s.pt.base = W := s.hpt
  have hx' : x.base = U := hx
  have hrb : Hom.base r.hom = eqToHom hr ≫ f ≫ eqToHom hx'.symm :=
    base_eq_of_isHomLift r.hom _ r.isHomLift
  have hsb : Hom.base s.hom = eqToHom hs ≫ (g ≫ f) ≫ eqToHom hx'.symm :=
    base_eq_of_isHomLift s.hom _ s.isHomLift
  have hb' : Hom.base ψ = eqToHom hs ≫ g ≫ eqToHom hr.symm := hb
  refine Functor.Restriction.eq_compTo g f rfl r s ψ
    (IsHomLift.of_fac' _ g ψ s.hpt r.hpt hb) (Hom.ext ?_ hm)
  show Hom.base ψ ≫ Hom.base r.hom = Hom.base s.hom
  rw [hb', hrb, hsb]
  simp

end TorsorsFor

/-- Two morphisms of the site whose images under the Yoneda embedding are compared through
`eqToHom`s: the shape in which a morphism of bases transports a factorization through `U`. -/
theorem yoneda_map_comp_eqToHom {U X W Y V : BigFppfOver 𝒞 S hS} (m : X ⟶ Y) (a : X = W)
    (c : Y = V) (k : W ⟶ V) (hm : m = eqToHom a ≫ k ≫ eqToHom c.symm) (g₀ : V ⟶ U)
    (g₁ : W ⟶ U) (hg : g₁ = k ≫ g₀) :
    yoneda.map m ≫ yoneda.map (eqToHom c ≫ g₀) = yoneda.map (eqToHom a ≫ g₁) := by
  subst hm hg a c
  simp


/-! ### Gluing the sections of `B` of a descent datum -/

namespace PrincipalHomogeneousSpaces

open TorsorsFor

/-- The sections of `B` carried by the objects of a descent datum of `G-Principal` along a
covering family of `U` glue to a single section `b : U ⟶ B`, because `B` is a sheaf and the
morphisms of `G-Principal` are morphisms over `B`. -/
theorem exists_glued_sec {U : BigFppfOver 𝒞 S hS} {I : Type w} {V : I → BigFppfOver 𝒞 S hS}
    {f : ∀ i, V i ⟶ U} (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U)
    {Vij : I → I → BigFppfOver 𝒞 S hS} {pr₁ : ∀ i j, Vij i j ⟶ V i}
    {pr₂ : ∀ i j, Vij i j ⟶ V j} {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
    {Vijk : I → I → I → BigFppfOver 𝒞 S hS}
    {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
    {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
    {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
    {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
    {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
    {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
    {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}
    (D : Functor.DescentDatum (projection hB G) V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
      q₁ q₂ q₃ hq₁ hq₂ hq₃) :
    ∃ b : yoneda.obj U ⟶ B, ∀ i,
      yoneda.map (eqToHom (show (D.x i).base = V i from D.hx i) ≫ f i) ≫ b = (D.x i).sec := by
  let τ : ∀ i, yoneda.obj (V i) ⟶ B := fun i => normalizedSection (D.x i) (D.hx i)
  have hxb : ∀ i, (D.x i).base = V i := D.hx
  have compat : ∀ i j, yoneda.map (pr₁ i j) ≫ τ i = yoneda.map (pr₂ i j) ≫ τ j := by
    intro i j
    have h₁ : (D.xrij i j).pt.base = Vij i j := (D.xrij i j).hpt
    have h₂ : (D.xrji i j).pt.base = Vij i j := (D.xrji i j).hpt
    have e₁ := comp_normalizedSection h₁ (hxb i) (D.xrij i j).hom (pr₁ i j)
      (base_eq_of_isHomLift _ _ (D.xrij i j).isHomLift)
    have e₂ := comp_normalizedSection h₂ (hxb j) (D.xrji i j).hom (pr₂ i j)
      (base_eq_of_isHomLift _ _ (D.xrji i j).isHomLift)
    have hφb : Hom.base (D.φ i j) = eqToHom h₁ ≫ 𝟙 _ ≫ eqToHom h₂.symm := by
      rw [Category.id_comp]
      exact base_eq_of_isHomLift _ _ (D.φ_fibreHom i j)
    have e₃ := comp_normalizedSection h₁ h₂ (D.φ i j) (𝟙 _) hφb
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at e₃
    exact e₁.trans (e₃.symm.trans e₂.symm)
  have hU : CategoryTheory.Presheaf.IsJointlyLocallySurjective (BigFppfOver.topology 𝒞 S hS)
      (fun i => yoneda.map (f i)) :=
    CategoryTheory.Presheaf.isJointlyLocallySurjective_of_isPullback _ (𝟙 (yoneda.obj U)) f hf
      (fun i => yoneda.map (f i)) (fun i => 𝟙 (yoneda.obj (V i)))
      (fun i => IsPullback.id_vert _)
  obtain ⟨b, hb, -⟩ := hU.existsUnique_hom hB.isSheaf τ (by
    intro W i j s t hst
    change s ≫ f i = t ≫ f j at hst
    let l := (hVij i j).lift s t hst
    have hl₁ : l ≫ pr₁ i j = s := (hVij i j).lift_fst s t hst
    have hl₂ : l ≫ pr₂ i j = t := (hVij i j).lift_snd s t hst
    have := congrArg (fun k => k.app (Opposite.op W) l) (compat i j)
    change (τ i).app (Opposite.op W) (l ≫ pr₁ i j) =
      (τ j).app (Opposite.op W) (l ≫ pr₂ i j) at this
    rwa [hl₁, hl₂] at this)
  refine ⟨b, fun i => ?_⟩
  calc yoneda.map (eqToHom (hxb i) ≫ f i) ≫ b
      = yoneda.map (eqToHom (hxb i)) ≫ (yoneda.map (f i) ≫ b) := by
        rw [CategoryTheory.Functor.map_comp, Category.assoc]
    _ = (D.x i).sec := by
        rw [hb i]
        show yoneda.map (eqToHom (hxb i)) ≫ yoneda.map (eqToHom (hxb i).symm) ≫ (D.x i).sec = _
        rw [← Category.assoc, ← CategoryTheory.Functor.map_comp, eqToHom_trans, eqToHom_refl,
          CategoryTheory.Functor.map_id, Category.id_comp]

end PrincipalHomogeneousSpaces


/-! ### Reading restrictions and descent data over `b` as data under `U ×_{b, B} G` -/

namespace PrincipalHomogeneousSpaces

open TorsorsFor

/-- A morphism of the fibre category is an isomorphism. -/
theorem isIso_of_fibreHom {T T' : PrincipalHomogeneousSpaces hB G} {V : BigFppfOver 𝒞 S hS}
    (φ : T ⟶ T') (ha : (projection hB G).obj T = V) (hb : (projection hB G).obj T' = V)
    (h : Functor.FibreHom (projection hB G) T T' ha hb φ) : IsIso φ := by
  have ha' : T.base = V := ha
  have hb' : T'.base = V := hb
  have hbase : Hom.base φ = eqToHom ha' ≫ eqToHom hb'.symm := base_eq_of_isHomLift _ _ h
  have : IsIso (Hom.base φ) := by rw [hbase, eqToHom_trans]; infer_instance
  exact isIso_of_isIso_base φ

/-- The morphism of bases of a morphism of the fibre category, as the conjugate of an identity. -/
theorem base_eq_of_fibreHom {T T' : PrincipalHomogeneousSpaces hB G} {V : BigFppfOver 𝒞 S hS}
    (φ : T ⟶ T') (ha : (projection hB G).obj T = V) (hb : (projection hB G).obj T' = V)
    (h : Functor.FibreHom (projection hB G) T T' ha hb φ) :
    Hom.base φ = eqToHom (show T.base = V from ha) ≫ 𝟙 V ≫
      eqToHom (show T'.base = V from hb).symm := by
  rw [Category.id_comp]
  exact base_eq_of_isHomLift _ _ h

variable {U : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)

/-- A restriction of an object of `G-Principal` whose section of `B` factors through `b` again
has its section of `B` factoring through `b`. -/
theorem sec_restriction {V W : BigFppfOver 𝒞 S hS} (T : PrincipalHomogeneousSpaces hB G)
    (hT : (projection hB G).obj T = V) (g₀ : V ⟶ U)
    (hs : yoneda.map (eqToHom (show T.base = _ from hT) ≫ g₀) ≫ b = T.sec) (g : W ⟶ V)
    (r : Functor.Restriction (projection hB G) g T hT) :
    yoneda.map (eqToHom (show r.pt.base = _ from r.hpt) ≫ g ≫ g₀) ≫ b = r.pt.sec := by
  have e := yoneda_map_comp_eqToHom (Hom.base r.hom) r.hpt hT g
    (base_eq_of_isHomLift _ _ r.isHomLift) g₀ (g ≫ g₀) rfl
  exact (congrArg (· ≫ b) e.symm).trans ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) hs).trans (Hom.comp_sec r.hom)))

/-- A restriction of an object of `G-Principal` whose section factors through `b`, read as a
restriction of the corresponding principal homogeneous space under `U ×_{b, B} G`. -/
def ofBaseRestriction {V W : BigFppfOver 𝒞 S hS} (T : PrincipalHomogeneousSpaces hB G)
    (hT : (projection hB G).obj T = V) (g₀ : V ⟶ U)
    (hs : yoneda.map (eqToHom (show T.base = _ from hT) ≫ g₀) ≫ b = T.sec) (g : W ⟶ V)
    (r : Functor.Restriction (projection hB G) g T hT) :
    Functor.Restriction
      (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)) g
      (ofBase _ b T (yoneda.map (eqToHom (show T.base = _ from hT) ≫ g₀)) hs) hT :=
  restrictionOfBase _ _ _
    (projection_isFiberedInGroupoids (isAlgebraicSpace_yoneda 𝒞 S hS U)
      (fppfPullbackGroup hB G U b)) g
    (x := ofBase _ b T (yoneda.map (eqToHom (show T.base = _ from hT) ≫ g₀)) hs) hT
    (ofBase _ b r.pt (yoneda.map (eqToHom (show r.pt.base = _ from r.hpt) ≫ g ≫ g₀))
      (sec_restriction b T hT g₀ hs g r))
    r.hpt
    (ofBaseHom _ b r.hom _ _ _ _ (yoneda_map_comp_eqToHom (Hom.base r.hom) r.hpt hT g
      (base_eq_of_isHomLift _ _ r.isHomLift) g₀ (g ≫ g₀) rfl))
    (base_eq_of_isHomLift r.hom _ r.isHomLift)

/-- The comparison of two restrictions read under `U ×_{b, B} G` is the comparison of the two
restrictions in `G-Principal`. -/
theorem compTo_ofBaseRestriction {U' V W : BigFppfOver 𝒞 S hS}
    (T : PrincipalHomogeneousSpaces hB G) (hT : (projection hB G).obj T = U') (g₀ : U' ⟶ U)
    (hs : yoneda.map (eqToHom (show T.base = _ from hT) ≫ g₀) ≫ b = T.sec) (g : W ⟶ V)
    (f : V ⟶ U') {l : W ⟶ U'}
    (hl : l = g ≫ f) (r : Functor.Restriction (projection hB G) f T hT)
    (s : Functor.Restriction (projection hB G) l T hT) :
    Functor.Restriction.compTo _ g f hl (ofBaseRestriction b T hT g₀ hs f r)
        (ofBaseRestriction b T hT g₀ hs l s) =
      ofBaseHom _ b (Functor.Restriction.compTo _ g f hl r s) _ _
        (sec_restriction b T hT g₀ hs l s) (sec_restriction b T hT g₀ hs f r)
        (yoneda_map_comp_eqToHom _ s.hpt r.hpt g (Restriction.compTo_base T hT f g hl r s)
          (f ≫ g₀) (l ≫ g₀) (by rw [hl, Category.assoc])) :=
  by
  refine (eq_compTo_of g f hl (ofBaseRestriction b T hT g₀ hs f r)
    (ofBaseRestriction b T hT g₀ hs l s) _ ?_ ?_).symm
  · exact Restriction.compTo_base T hT f g hl r s
  · exact congrArg Hom.map (Functor.Restriction.compTo_hom _ g f hl r s)

/-- The comparison of a restriction with the identity restriction, read under
`U ×_{b, B} G`. -/
theorem compTo_id_ofBaseRestriction {U' W : BigFppfOver 𝒞 S hS}
    (T : PrincipalHomogeneousSpaces hB G) (hT : (projection hB G).obj T = U') (g₀ : U' ⟶ U)
    (hs : yoneda.map (eqToHom (show T.base = _ from hT) ≫ g₀) ≫ b = T.sec) (g : W ⟶ U') {l : W ⟶ U'}
    (hl : l = g ≫ 𝟙 U') (s : Functor.Restriction (projection hB G) l T hT) :
    Functor.Restriction.compTo
        (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)) g (𝟙 U') hl
        (Functor.Restriction.id _
          (ofBase _ b T (yoneda.map (eqToHom (show T.base = _ from hT) ≫ g₀)) hs) hT)
        (ofBaseRestriction b T hT g₀ hs l s) =
      ofBaseHom _ b (Functor.Restriction.compTo _ g (𝟙 U') hl (Functor.Restriction.id _ _ hT) s)
        _ _ (sec_restriction b T hT g₀ hs l s) hs
        (yoneda_map_comp_eqToHom _ s.hpt hT g
          (Restriction.compTo_base T hT (𝟙 U') g hl (Functor.Restriction.id _ _ hT) s)
          g₀ (l ≫ g₀) (by rw [hl, Category.comp_id])) :=
  by
  refine (eq_compTo_of g (𝟙 U') hl
    (Functor.Restriction.id _
      (ofBase _ b T (yoneda.map (eqToHom (show T.base = _ from hT) ≫ g₀)) hs) hT)
    (ofBaseRestriction b T hT g₀ hs l s) _ ?_ ?_).symm
  · exact Restriction.compTo_base T hT (𝟙 U') g hl (Functor.Restriction.id _ _ hT) s
  · exact congrArg Hom.map (Functor.Restriction.compTo_hom _ g (𝟙 U') hl
      (Functor.Restriction.id _ _ hT) s)

/-- A morphism of the fibre category of `G-Principal` lies over the identity when read under
`U ×_{b, B} G`. -/
theorem fibreHom_ofBaseHom {T₁ T₂ : PrincipalHomogeneousSpaces hB G} {V : BigFppfOver 𝒞 S hS}
    (φ : T₁ ⟶ T₂) (h₁ : (projection hB G).obj T₁ = V) (h₂ : (projection hB G).obj T₂ = V)
    (hφ : Functor.FibreHom (projection hB G) T₁ T₂ h₁ h₂ φ)
    (s₁ : yoneda.obj T₁.base ⟶ yoneda.obj U) (s₂ : yoneda.obj T₂.base ⟶ yoneda.obj U)
    (e₁ : s₁ ≫ b = T₁.sec) (e₂ : s₂ ≫ b = T₂.sec)
    (hs : yoneda.map (Hom.base φ) ≫ s₂ = s₁) :
    Functor.FibreHom (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b))
      (ofBase _ b T₁ s₁ e₁) (ofBase _ b T₂ s₂ e₂) h₁ h₂ (ofBaseHom _ b φ s₁ s₂ e₁ e₂ hs) := by
  refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact base_eq_of_isHomLift φ _ hφ

end PrincipalHomogeneousSpaces


namespace PrincipalHomogeneousSpaces

open TorsorsFor

/-- Transport of a factorization through `U` along a commutative square of the site, read
through the Yoneda embedding. -/
theorem yoneda_map_comp_of_comm {X Y X' Y' : BigFppfOver 𝒞 S hS}
    {Z : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} (t : X ⟶ Y) (c₁ : Y ⟶ Y') (c₂ : X ⟶ X')
    (a : X' ⟶ Y') (h : t ≫ c₁ = c₂ ≫ a) (N₁ : yoneda.obj Y' ⟶ Z) (N₂ : yoneda.obj X' ⟶ Z)
    (M₁ : yoneda.obj Y ⟶ Z) (M₂ : yoneda.obj X ⟶ Z) (L₁ : yoneda.map c₁ ≫ N₁ = M₁)
    (L₂ : yoneda.map a ≫ N₁ = N₂) (L₃ : yoneda.map c₂ ≫ N₂ = M₂) :
    yoneda.map t ≫ M₁ = M₂ := by
  rw [← L₁, ← L₃, ← L₂, ← Category.assoc, ← CategoryTheory.Functor.map_comp, h,
    CategoryTheory.Functor.map_comp, Category.assoc]

section ToBase

variable {U : BigFppfOver 𝒞 S hS} (b : yoneda.obj U ⟶ B)

/-- A restriction of a principal homogeneous space under `U ×_{b, B} G`, read as a restriction in
`G-Principal`. -/
def toBaseRestriction {V W : BigFppfOver 𝒞 S hS}
    (A : PrincipalHomogeneousSpaces (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b))
    (hA : (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)).obj A = V)
    (g : W ⟶ V)
    (r : Functor.Restriction
      (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)) g A hA) :
    Functor.Restriction (projection hB G) g (toBase _ b A) hA :=
  restrictionOfBase _ _ _ (projection_isFiberedInGroupoids hB G) g (x := toBase _ b A) hA
    (toBase _ b r.pt) r.hpt (toBaseHom _ b r.hom) (base_eq_of_isHomLift r.hom _ r.isHomLift)

/-- The comparison of two restrictions read in `G-Principal` is the comparison of the two
restrictions under `U ×_{b, B} G`. -/
theorem compTo_toBaseRestriction {U' V W : BigFppfOver 𝒞 S hS}
    (A : PrincipalHomogeneousSpaces (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b))
    (hA : (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)).obj A = U')
    (g : W ⟶ V) (f : V ⟶ U') {l : W ⟶ U'} (hl : l = g ≫ f)
    (r : Functor.Restriction
      (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)) f A hA)
    (s : Functor.Restriction
      (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)) l A hA) :
    Functor.Restriction.compTo _ g f hl (toBaseRestriction b A hA f r)
        (toBaseRestriction b A hA l s) =
      toBaseHom _ b (Functor.Restriction.compTo _ g f hl r s) := by
  refine (eq_compTo_of g f hl (toBaseRestriction b A hA f r)
    (toBaseRestriction b A hA l s) _ ?_ ?_).symm
  · exact Restriction.compTo_base A hA f g hl r s
  · exact congrArg Hom.map (Functor.Restriction.compTo_hom _ g f hl r s)

/-- The morphism of bases of a morphism to an object read back from `U ×_{b, B} G`. -/
theorem base_toBaseHom_comp
    {A : PrincipalHomogeneousSpaces (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)}
    {T : PrincipalHomogeneousSpaces hB G} {s : yoneda.obj T.base ⟶ yoneda.obj U}
    {hs : s ≫ b = T.sec} (ψ : A ⟶ ofBase _ b T s hs) :
    Hom.base (toBaseHom _ b ψ ≫ toBaseOfBase _ b T s hs) = Hom.base ψ :=
  Category.comp_id _

/-- The morphism of total spaces of a morphism to an object read back from `U ×_{b, B} G`. -/
theorem map_toBaseHom_comp
    {A : PrincipalHomogeneousSpaces (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)}
    {T : PrincipalHomogeneousSpaces hB G} {s : yoneda.obj T.base ⟶ yoneda.obj U}
    {hs : s ≫ b = T.sec} (ψ : A ⟶ ofBase _ b T s hs) :
    Hom.map (toBaseHom _ b ψ ≫ toBaseOfBase _ b T s hs) = Hom.map ψ :=
  Category.comp_id _

/-- A morphism of the fibre category under `U ×_{b, B} G` to an object read from `G-Principal`
gives a morphism of the fibre category of `G-Principal`. -/
theorem fibreHom_toBaseHom_comp {V : BigFppfOver 𝒞 S hS}
    {A : PrincipalHomogeneousSpaces (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)}
    {T : PrincipalHomogeneousSpaces hB G} {s : yoneda.obj T.base ⟶ yoneda.obj U}
    {hs : s ≫ b = T.sec} (ψ : A ⟶ ofBase _ b T s hs)
    (h₁ : (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)).obj A = V)
    (h₂ : (projection hB G).obj T = V)
    (hψ : Functor.FibreHom
      (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)) A
      (ofBase _ b T s hs) h₁ h₂ ψ) :
    Functor.FibreHom (projection hB G) (toBase _ b A) T h₁ h₂
      (toBaseHom _ b ψ ≫ toBaseOfBase _ b T s hs) := by
  refine IsHomLift.of_fac' _ _ _ rfl rfl ?_
  rw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (base_toBaseHom_comp b ψ).trans (base_eq_of_isHomLift ψ _ hψ)

/-- A canonical restriction under `U ×_{b, B} G` of a morphism into an object read from
`G-Principal`, read back in `G-Principal`. -/
theorem isRestrictionOf_toBase {Ux V W : BigFppfOver 𝒞 S hS}
    (A : PrincipalHomogeneousSpaces (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b))
    (hA : (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)).obj A = Ux)
    (T : PrincipalHomogeneousSpaces hB G) (hT : (projection hB G).obj T = V) (g₀ : V ⟶ U)
    (hs : yoneda.map (eqToHom (show T.base = V from hT) ≫ g₀) ≫ b = T.sec)
    (fx : V ⟶ Ux) (g : W ⟶ V) {mx : W ⟶ Ux} (hfx : mx = g ≫ fx) (hfy : g = g ≫ 𝟙 V)
    (xr' : Functor.Restriction
      (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)) fx A hA)
    (xrW' : Functor.Restriction
      (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)) mx A hA)
    (rT : Functor.Restriction (projection hB G) g T hT)
    (ψ' : xr'.pt ⟶ ofBase _ b T _ hs) (ψW' : xrW'.pt ⟶ (ofBaseRestriction b T hT g₀ hs g rT).pt)
    (h : Functor.IsRestrictionOf _ g hfx hfy xr'
      (Functor.Restriction.id _
        (ofBase _ b T (yoneda.map (eqToHom (show T.base = V from hT) ≫ g₀)) hs) hT) xrW'
      (ofBaseRestriction b T hT g₀ hs g rT) ψ' ψW') :
    Functor.IsRestrictionOf (projection hB G) g hfx hfy (toBaseRestriction b A hA fx xr')
      (Functor.Restriction.id _ T hT) (toBaseRestriction b A hA mx xrW') rT
      (toBaseHom _ b ψ' ≫ toBaseOfBase _ b T _ hs)
      (toBaseHom _ b ψW' ≫ toBaseOfBase _ b rT.pt _ (sec_restriction b T hT g₀ hs g rT)) := by
  have L := compTo_toBaseRestriction b A hA g fx hfx xr' xrW'
  have Lid := compTo_id_ofBaseRestriction b T hT g₀ hs g hfy rT
  have h' := (congrArg (ψW' ≫ ·) Lid.symm).trans h
  show _ ≫ _ = _ ≫ _
  refine Eq.trans ?_ (congrArg (· ≫ _) L.symm)
  refine Hom.ext ?_ ?_
  · have e := congrArg Hom.base h'
    simp only [Hom.base_comp] at e ⊢
    exact (congrArg (· ≫ _) (Category.comp_id _)).trans (e.trans
      (congrArg (_ ≫ ·) (Category.comp_id _).symm))
  · have e := congrArg Hom.map h'
    simp only [Hom.map_comp] at e ⊢
    exact (congrArg (· ≫ _) (Category.comp_id _)).trans (e.trans
      (congrArg (_ ≫ ·) (Category.comp_id _).symm))

/-- Compatibility with a gluing isomorphism, read back in `G-Principal`. -/
theorem comp_toBase_eq
    {A : PrincipalHomogeneousSpaces (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)}
    {T₁ T₂ : PrincipalHomogeneousSpaces hB G}
    {s₁ : yoneda.obj T₁.base ⟶ yoneda.obj U} {s₂ : yoneda.obj T₂.base ⟶ yoneda.obj U}
    {h₁ : s₁ ≫ b = T₁.sec} {h₂ : s₂ ≫ b = T₂.sec} (φ : T₁ ⟶ T₂)
    (hφ : yoneda.map (Hom.base φ) ≫ s₂ = s₁)
    (ψ₁ : A ⟶ ofBase _ b T₁ s₁ h₁) (ψ₂ : A ⟶ ofBase _ b T₂ s₂ h₂)
    (e : ψ₁ ≫ ofBaseHom _ b φ s₁ s₂ h₁ h₂ hφ = ψ₂) :
    (toBaseHom _ b ψ₁ ≫ toBaseOfBase _ b T₁ s₁ h₁) ≫ φ =
      toBaseHom _ b ψ₂ ≫ toBaseOfBase _ b T₂ s₂ h₂ := by
  refine Hom.ext ?_ ?_
  · have e' := congrArg Hom.base e
    simp only [Hom.base_comp, toBaseHom_base, toBaseOfBase_base, ofBaseHom_base] at e' ⊢
    simpa using e'
  · have e' := congrArg Hom.map e
    simp only [Hom.map_comp, toBaseHom_map, toBaseOfBase_map, ofBaseHom_map] at e' ⊢
    simpa using e'

end ToBase

section DescentDatum

variable {U : BigFppfOver 𝒞 S hS} {I : Type w} {V : I → BigFppfOver 𝒞 S hS}
  {f : ∀ i, V i ⟶ U}
  {Vij : I → I → BigFppfOver 𝒞 S hS} {pr₁ : ∀ i j, Vij i j ⟶ V i}
  {pr₂ : ∀ i j, Vij i j ⟶ V j} {hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j)}
  {Vijk : I → I → I → BigFppfOver 𝒞 S hS}
  {s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j} {s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k}
  {hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k)}
  {q₁ : ∀ i j k, Vijk i j k ⟶ V i} {q₂ : ∀ i j k, Vijk i j k ⟶ V j}
  {q₃ : ∀ i j k, Vijk i j k ⟶ V k}
  {hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j}
  {hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j}
  {hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k}

variable (b : yoneda.obj U ⟶ B)

/-- A descent datum of `G-Principal` along a covering family of `U` whose sections of `B` factor
through `b : U ⟶ B`, read as a descent datum of principal homogeneous spaces under
`H = U ×_{b, B} G`: every object keeps its total space and its morphisms, and its acting group
`V_i ×_{b_i, B} G` is identified with `V_i ×_U H` by `groupCompIso`. -/
def descentDatumOfBase
    (D : Functor.DescentDatum (projection hB G) V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
      q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (hb : ∀ i, yoneda.map (eqToHom (show (D.x i).base = V i from D.hx i) ≫ f i) ≫ b = (D.x i).sec) :
    Functor.DescentDatum
      (projection (isAlgebraicSpace_yoneda 𝒞 S hS U) (fppfPullbackGroup hB G U b)) V f Vij
      pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ where
  x i := ofBase _ b (D.x i)
    (yoneda.map (eqToHom (show (D.x i).base = V i from D.hx i) ≫ f i)) (hb i)
  hx := D.hx
  xrij i j := ofBaseRestriction b (D.x i) (D.hx i) (f i) (hb i) (pr₁ i j) (D.xrij i j)
  xrji i j := ofBaseRestriction b (D.x j) (D.hx j) (f j) (hb j) (pr₂ i j) (D.xrji i j)
  φ i j := ofBaseHom _ b (D.φ i j)
    (yoneda.map (eqToHom (show (D.xrij i j).pt.base = _ from (D.xrij i j).hpt) ≫ pr₁ i j ≫ f i))
    (yoneda.map (eqToHom (show (D.xrji i j).pt.base = _ from (D.xrji i j).hpt) ≫ pr₂ i j ≫ f j))
    (sec_restriction b (D.x i) (D.hx i) (f i) (hb i) (pr₁ i j) (D.xrij i j))
    (sec_restriction b (D.x j) (D.hx j) (f j) (hb j) (pr₂ i j) (D.xrji i j))
    (yoneda_map_comp_eqToHom _ (D.xrij i j).hpt (D.xrji i j).hpt (𝟙 _)
      (base_eq_of_fibreHom _ _ _ (D.φ_fibreHom i j)) (pr₂ i j ≫ f j) (pr₁ i j ≫ f i)
      (by rw [Category.id_comp, (hVij i j).w]))
  φ_fibreHom i j := fibreHom_ofBaseHom b _ _ _ (D.φ_fibreHom i j) _ _ _ _ _
  φ_iso i j := isIso_of_fibreHom _ _ _ (fibreHom_ofBaseHom b _ _ _ (D.φ_fibreHom i j) _ _ _ _ _)
  wi i j k := ofBaseRestriction b (D.x i) (D.hx i) (f i) (hb i) (q₁ i j k) (D.wi i j k)
  wj i j k := ofBaseRestriction b (D.x j) (D.hx j) (f j) (hb j) (q₂ i j k) (D.wj i j k)
  wk i j k := ofBaseRestriction b (D.x k) (D.hx k) (f k) (hb k) (q₃ i j k) (D.wk i j k)
  αij i j k := ofBaseHom _ b (D.αij i j k)
    (yoneda.map (eqToHom (show (D.wi i j k).pt.base = _ from (D.wi i j k).hpt) ≫ q₁ i j k ≫ f i))
    (yoneda.map (eqToHom (show (D.wj i j k).pt.base = _ from (D.wj i j k).hpt) ≫ q₂ i j k ≫ f j))
    (sec_restriction b (D.x i) (D.hx i) (f i) (hb i) (q₁ i j k) (D.wi i j k))
    (sec_restriction b (D.x j) (D.hx j) (f j) (hb j) (q₂ i j k) (D.wj i j k))
    (yoneda_map_comp_of_comm _ _ _ _ (congrArg Hom.base (D.αij_restr i j k) :) _ _ _ _
      (yoneda_map_comp_eqToHom _ (D.wj i j k).hpt (D.xrji i j).hpt (s₁₂ i j k)
        (Restriction.compTo_base (D.x j) (D.hx j) (pr₂ i j) (s₁₂ i j k) (hq₂ i j k) (D.xrji i j)
          (D.wj i j k))
        (pr₂ i j ≫ f j) (q₂ i j k ≫ f j) (by rw [hq₂, Category.assoc]))
      (yoneda_map_comp_eqToHom _ (D.xrij i j).hpt (D.xrji i j).hpt (𝟙 _)
        (base_eq_of_fibreHom _ _ _ (D.φ_fibreHom i j))
        (pr₂ i j ≫ f j) (pr₁ i j ≫ f i) (by rw [Category.id_comp, (hVij i j).w]))
      (yoneda_map_comp_eqToHom _ (D.wi i j k).hpt (D.xrij i j).hpt (s₁₂ i j k)
        (Restriction.compTo_base (D.x i) (D.hx i) (pr₁ i j) (s₁₂ i j k) (hq₁ i j k) (D.xrij i j)
          (D.wi i j k))
        (pr₁ i j ≫ f i) (q₁ i j k ≫ f i) (by rw [hq₁, Category.assoc])))
  αjk i j k := ofBaseHom _ b (D.αjk i j k)
    (yoneda.map (eqToHom (show (D.wj i j k).pt.base = _ from (D.wj i j k).hpt) ≫ q₂ i j k ≫ f j))
    (yoneda.map (eqToHom (show (D.wk i j k).pt.base = _ from (D.wk i j k).hpt) ≫ q₃ i j k ≫ f k))
    (sec_restriction b (D.x j) (D.hx j) (f j) (hb j) (q₂ i j k) (D.wj i j k))
    (sec_restriction b (D.x k) (D.hx k) (f k) (hb k) (q₃ i j k) (D.wk i j k))
    (yoneda_map_comp_of_comm _ _ _ _ (congrArg Hom.base (D.αjk_restr i j k) :) _ _ _ _
      (yoneda_map_comp_eqToHom _ (D.wk i j k).hpt (D.xrji j k).hpt (s₂₃ i j k)
        (Restriction.compTo_base (D.x k) (D.hx k) (pr₂ j k) (s₂₃ i j k) (hq₃ i j k) (D.xrji j k)
          (D.wk i j k))
        (pr₂ j k ≫ f k) (q₃ i j k ≫ f k) (by rw [hq₃, Category.assoc]))
      (yoneda_map_comp_eqToHom _ (D.xrij j k).hpt (D.xrji j k).hpt (𝟙 _)
        (base_eq_of_fibreHom _ _ _ (D.φ_fibreHom j k))
        (pr₂ j k ≫ f k) (pr₁ j k ≫ f j) (by rw [Category.id_comp, (hVij j k).w]))
      (yoneda_map_comp_eqToHom _ (D.wj i j k).hpt (D.xrij j k).hpt (s₂₃ i j k)
        (Restriction.compTo_base (D.x j) (D.hx j) (pr₁ j k) (s₂₃ i j k)
          ((hq₂ i j k).trans (hVijk i j k).w) (D.xrij j k) (D.wj i j k))
        (pr₁ j k ≫ f j) (q₂ i j k ≫ f j) (by rw [hq₂, (hVijk i j k).w, Category.assoc])))
  αik i j k := ofBaseHom _ b (D.αik i j k)
    (yoneda.map (eqToHom (show (D.wi i j k).pt.base = _ from (D.wi i j k).hpt) ≫ q₁ i j k ≫ f i))
    (yoneda.map (eqToHom (show (D.wk i j k).pt.base = _ from (D.wk i j k).hpt) ≫ q₃ i j k ≫ f k))
    (sec_restriction b (D.x i) (D.hx i) (f i) (hb i) (q₁ i j k) (D.wi i j k))
    (sec_restriction b (D.x k) (D.hx k) (f k) (hb k) (q₃ i j k) (D.wk i j k))
    (yoneda_map_comp_of_comm _ _ _ _ (congrArg Hom.base (D.αik_restr i j k) :) _ _ _ _
      (yoneda_map_comp_eqToHom _ (D.wk i j k).hpt (D.xrji i k).hpt (D.s₁₃ i j k)
        (Restriction.compTo_base (D.x k) (D.hx k) (pr₂ i k) (D.s₁₃ i j k) (D.hs₁₃₂ i j k).symm
          (D.xrji i k) (D.wk i j k))
        (pr₂ i k ≫ f k) (q₃ i j k ≫ f k) (by rw [← D.hs₁₃₂, Category.assoc]))
      (yoneda_map_comp_eqToHom _ (D.xrij i k).hpt (D.xrji i k).hpt (𝟙 _)
        (base_eq_of_fibreHom _ _ _ (D.φ_fibreHom i k))
        (pr₂ i k ≫ f k) (pr₁ i k ≫ f i) (by rw [Category.id_comp, (hVij i k).w]))
      (yoneda_map_comp_eqToHom _ (D.wi i j k).hpt (D.xrij i k).hpt (D.s₁₃ i j k)
        (Restriction.compTo_base (D.x i) (D.hx i) (pr₁ i k) (D.s₁₃ i j k) (D.hs₁₃₁ i j k).symm
          (D.xrij i k) (D.wi i j k))
        (pr₁ i k ≫ f i) (q₁ i j k ≫ f i) (by rw [← D.hs₁₃₁, Category.assoc])))
  αij_restr i j k := by
    change _ ≫ _ = _ ≫ _
    refine (congrArg (_ ≫ ·) (compTo_ofBaseRestriction b (D.x j) (D.hx j) (f j) (hb j) (s₁₂ i j k)
      (pr₂ i j) (hq₂ i j k) (D.xrji i j) (D.wj i j k))).trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ _) (compTo_ofBaseRestriction b (D.x i) (D.hx i) (f i) (hb i)
      (s₁₂ i j k) (pr₁ i j) (hq₁ i j k) (D.xrij i j) (D.wi i j k)).symm)
    exact Hom.ext (congrArg Hom.base (D.αij_restr i j k) :) (congrArg Hom.map (D.αij_restr i j k) :)
  αjk_restr i j k := by
    change _ ≫ _ = _ ≫ _
    refine (congrArg (_ ≫ ·) (compTo_ofBaseRestriction b (D.x k) (D.hx k) (f k) (hb k) (s₂₃ i j k)
      (pr₂ j k) (hq₃ i j k) (D.xrji j k) (D.wk i j k))).trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ _) (compTo_ofBaseRestriction b (D.x j) (D.hx j) (f j) (hb j)
      (s₂₃ i j k) (pr₁ j k) ((hq₂ i j k).trans (hVijk i j k).w) (D.xrij j k) (D.wj i j k)).symm)
    exact Hom.ext (congrArg Hom.base (D.αjk_restr i j k) :) (congrArg Hom.map (D.αjk_restr i j k) :)
  s₁₃ := D.s₁₃
  hs₁₃₁ := D.hs₁₃₁
  hs₁₃₂ := D.hs₁₃₂
  αik_restr i j k := by
    change _ ≫ _ = _ ≫ _
    refine (congrArg (_ ≫ ·) (compTo_ofBaseRestriction b (D.x k) (D.hx k) (f k) (hb k) (D.s₁₃ i j k)
      (pr₂ i k) (D.hs₁₃₂ i j k).symm (D.xrji i k) (D.wk i j k))).trans ?_
    refine Eq.trans ?_ (congrArg (· ≫ _) (compTo_ofBaseRestriction b (D.x i) (D.hx i) (f i) (hb i)
      (D.s₁₃ i j k) (pr₁ i k) (D.hs₁₃₁ i j k).symm (D.xrij i k) (D.wi i j k)).symm)
    exact Hom.ext (congrArg Hom.base (D.αik_restr i j k) :) (congrArg Hom.map (D.αik_restr i j k) :)
  cocycle i j k :=
    Hom.ext (congrArg Hom.base (D.cocycle i j k) :) (congrArg Hom.map (D.cocycle i j k) :)

/-- If the descent datum read under `H = U ×_{b, B} G` is effective, so is the descent datum of
`G-Principal`: the descended principal homogeneous space under `H` is read back as an object of
`G-Principal`, with the same total space and the same morphisms. -/
theorem isEffective_of_isEffective_descentDatumOfBase
    (D : Functor.DescentDatum (projection hB G) V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk
      q₁ q₂ q₃ hq₁ hq₂ hq₃)
    (hb : ∀ i, yoneda.map (eqToHom (show (D.x i).base = V i from D.hx i) ≫ f i) ≫ b = (D.x i).sec)
    (h : (descentDatumOfBase b D hb).IsEffective) : D.IsEffective := by
  obtain ⟨x', hx', xr', ψ', hψf, -, hov⟩ := h
  have hfib : ∀ i, Functor.FibreHom (projection hB G) (toBase _ b (xr' i).pt) (D.x i)
      (xr' i).hpt (D.hx i) (toBaseHom _ b (ψ' i) ≫ toBaseOfBase _ b (D.x i) _ (hb i)) :=
    fun i => fibreHom_toBaseHom_comp b (ψ' i) (xr' i).hpt (D.hx i) (hψf i)
  refine ⟨toBase _ b x', hx', fun i => toBaseRestriction b x' hx' (f i) (xr' i),
    fun i => toBaseHom _ b (ψ' i) ≫ toBaseOfBase _ b (D.x i) _ (hb i), hfib,
    fun i => isIso_of_fibreHom _ _ _ (hfib i), fun i j => ?_⟩
  obtain ⟨x'rij, ψ'ir, ψ'jr, f₁, f₂, -, -, r₁, r₂, e⟩ := hov i j
  have hir := sec_restriction b (D.x i) (D.hx i) (f i) (hb i) (pr₁ i j) (D.xrij i j)
  have hjr := sec_restriction b (D.x j) (D.hx j) (f j) (hb j) (pr₂ i j) (D.xrji i j)
  have g₁ := fibreHom_toBaseHom_comp b ψ'ir x'rij.hpt (D.xrij i j).hpt f₁
  have g₂ := fibreHom_toBaseHom_comp b ψ'jr x'rij.hpt (D.xrji i j).hpt f₂
  refine ⟨toBaseRestriction b x' hx' _ x'rij, toBaseHom _ b ψ'ir ≫ toBaseOfBase _ b _ _ hir,
    toBaseHom _ b ψ'jr ≫ toBaseOfBase _ b _ _ hjr, g₁, g₂, isIso_of_fibreHom _ _ _ g₁,
    isIso_of_fibreHom _ _ _ g₂, ?_, ?_, ?_⟩
  · exact isRestrictionOf_toBase b x' hx' (D.x i) (D.hx i) (f i) (hb i) (f i) (pr₁ i j) rfl
      (by simp) (xr' i) x'rij (D.xrij i j) (ψ' i) ψ'ir r₁
  · exact isRestrictionOf_toBase b x' hx' (D.x j) (D.hx j) (f j) (hb j) (f j) (pr₂ i j)
      (hVij i j).w (by simp) (xr' j) x'rij (D.xrji i j) (ψ' j) ψ'jr r₂
  · exact comp_toBase_eq b (A := x'rij.pt) (h₁ := hir) (h₂ := hjr) (D.φ i j)
      (yoneda_map_comp_eqToHom _ (D.xrij i j).hpt (D.xrji i j).hpt (𝟙 _)
        (base_eq_of_fibreHom _ _ _ (D.φ_fibreHom i j)) (pr₂ i j ≫ f j) (pr₁ i j ≫ f i)
        (by rw [Category.id_comp, (hVij i j).w])) ψ'ir ψ'jr e

end DescentDatum

end PrincipalHomogeneousSpaces


/-! ### Stacks 04UP -/

variable (𝒞 S hS) in
/-- **Effective descent of principal homogeneous spaces along fppf coverings**, items (1)–(4) of
Stacks 04UP: given

1. a covering `{fᵢ : Uᵢ ⟶ U}` of the big fppf site of `S`,
2. a group algebraic space `H` over `U`,
3. for every `i` a principal homogeneous `H_{Uᵢ}`-space `Xᵢ` over `Uᵢ`, and
4. `H`-equivariant isomorphisms `φᵢⱼ : Xᵢ|_{Uᵢ ×_U Uⱼ} ⟶ Xⱼ|_{Uᵢ ×_U Uⱼ}` satisfying the cocycle
   condition over the triple overlaps,

there is a principal homogeneous `H`-space `X` over `U` which recovers `(Xᵢ, φᵢⱼ)`.

Items (3) and (4) are a descent datum `D` of the category `H-Principal` of Stacks 04UN for the
group algebraic space `H` over the algebraic space `U` itself, along the covering family, whose
objects lie over the members of the covering: `D.x i` is a principal homogeneous space over `Uᵢ`
under `Uᵢ ×_{fᵢ, U} H = H_{Uᵢ}`, the hypothesis on the sections saying that its morphism to `U` is
`fᵢ`; the morphisms `D.φ i j` of the fibre categories over the double overlaps are exactly the
`H`-equivariant isomorphisms between the restrictions, and `D.cocycle` is the cocycle condition.
"Recovers" is effectivity of `D` (`CategoryTheory.Functor.DescentDatum.IsEffective`): an object
`X` of `H-Principal` over `U` together with isomorphisms of its restrictions to the `Uᵢ` with the
`Xᵢ`, compatible with the `φᵢⱼ`. Its morphism to `U` is then the identity, because the restrictions
of a morphism to `U` along a covering family determine it, so `X` is a principal homogeneous space
under `U ×_U H = H`.

Stacks does not know whether this holds: the remark says that the technique of the proof of
Stacks 04U1 reduces it to a set theoretical question, namely bounding the size of an atlas of the
glued sheaf, which for a principal homogeneous space trivialized only fpqc locally the technique
does not provide. It is the open part of Stacks 04UP, which is the implication proved in
`AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.isStackInGroupoids_of_descent`. -/
def PrincipalHomogeneousSpaceDescent : Prop :=
  ∀ (U : BigFppfOver 𝒞 S hS)
    (H : GroupAlgebraicSpace 𝒞 S hS (yoneda.obj U) (isAlgebraicSpace_yoneda 𝒞 S hS U))
    {I : Type w} (V : I → BigFppfOver 𝒞 S hS) (f : ∀ i, V i ⟶ U),
    Sieve.ofArrows V f ∈ BigFppfOver.topology 𝒞 S hS U →
    ∀ (Vij : I → I → BigFppfOver 𝒞 S hS)
      (pr₁ : ∀ i j, Vij i j ⟶ V i) (pr₂ : ∀ i j, Vij i j ⟶ V j)
      (hVij : ∀ i j, IsPullback (pr₁ i j) (pr₂ i j) (f i) (f j))
      (Vijk : I → I → I → BigFppfOver 𝒞 S hS)
      (s₁₂ : ∀ i j k, Vijk i j k ⟶ Vij i j) (s₂₃ : ∀ i j k, Vijk i j k ⟶ Vij j k)
      (hVijk : ∀ i j k, IsPullback (s₁₂ i j k) (s₂₃ i j k) (pr₂ i j) (pr₁ j k))
      (q₁ : ∀ i j k, Vijk i j k ⟶ V i) (q₂ : ∀ i j k, Vijk i j k ⟶ V j)
      (q₃ : ∀ i j k, Vijk i j k ⟶ V k)
      (hq₁ : ∀ i j k, q₁ i j k = s₁₂ i j k ≫ pr₁ i j)
      (hq₂ : ∀ i j k, q₂ i j k = s₁₂ i j k ≫ pr₂ i j)
      (hq₃ : ∀ i j k, q₃ i j k = s₂₃ i j k ≫ pr₂ j k)
      (D : Functor.DescentDatum
        (PrincipalHomogeneousSpaces.projection (isAlgebraicSpace_yoneda 𝒞 S hS U) H)
        V f Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃),
      (∀ i, (D.x i).sec = yoneda.map (eqToHom (show (D.x i).base = V i from D.hx i) ≫ f i)) →
        D.IsEffective

namespace PrincipalHomogeneousSpaces

variable (hB G) in
/-- **Stacks 04UP.** If principal homogeneous spaces satisfy effective descent along the
coverings of `(Sch/S)_fppf` (items (1)–(4) of the remark,
`AlgebraicGeometry.Space.PrincipalHomogeneousSpaceDescent`), then
`p : G-Principal ⥤ (Sch/S)_fppf` is a stack in groupoids over `(Sch/S)_fppf`.

This is the formal content of the remark: Stacks conjectures that `p` is a stack in groupoids and
says that this would follow from the descent statement (1)–(4), whose proof by the technique of
Stacks 04U1 stops at a set theoretical question; that descent statement is the antecedent here,
and the implication is proved in full.

* Condition (1) of Stacks 02ZI, that `p` is fibred in groupoids, is
  `AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.projection_isFiberedInGroupoids`.
* Condition (2), that the `Isom` presheaves are sheaves, is
  `AlgebraicGeometry.Space.TorsorsFor.projection_isomIsSheaf` at the fpqc coverings: isomorphisms
  of total spaces glue because the total spaces are algebraic spaces, hence sheaves.
* Condition (3): given a descent datum of `G-Principal` along a covering `{Vᵢ ⟶ U}`, the sections
  `bᵢ : Vᵢ ⟶ B` glue to `b : U ⟶ B` because `B` is a sheaf
  (`AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.exists_glued_sec`); with
  `H = U ×_{b, B} G` the acting groups `Vᵢ ×_{bᵢ, B} G` are identified with `H_{Vᵢ}`
  (`AlgebraicGeometry.Space.groupCompIso`), which turns the datum into one of the shape (1)–(4)
  (`AlgebraicGeometry.Space.PrincipalHomogeneousSpaces.descentDatumOfBase`); the antecedent makes
  it effective, and the descended principal homogeneous `H`-space read back in `G-Principal`
  makes the original datum effective
  (`PrincipalHomogeneousSpaces.isEffective_of_isEffective_descentDatumOfBase`).

"Up to a replacement as in Stacks 03ZZ" is not needed: an object of `G-Principal` carries as total
space an object of the slice over a representable presheaf of the set-sized big fppf site, so
`G-Principal` is a genuine category and `p` a functor, as for Stacks 04US. -/
@[stacks 04UP "p : G-Principal ⥤ (Sch/S)_fppf is a stack in groupoids once principal homogeneous \
spaces descend along fppf coverings as in (1)-(4)"]
theorem isStackInGroupoids_of_descent (h : PrincipalHomogeneousSpaceDescent.{w} 𝒞 S hS) :
    Functor.IsStackInGroupoids.{w} (projection hB G) (BigFppfOver.topology 𝒞 S hS) where
  isFiberedInGroupoids := projection_isFiberedInGroupoids hB G
  isom_isSheaf := by
    intro U x y hx hy I V f hf Vij pr₁ pr₂ hVij xr yr xrij yrij
    exact TorsorsFor.projection_isomIsSheaf hB G _ x y hx hy V f hf Vij pr₁ pr₂ hVij xr yr
      xrij yrij
  effective_descent := by
    intro U I V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃ hq₁ hq₂ hq₃ D
    obtain ⟨b, hb⟩ := exists_glued_sec hf D
    exact isEffective_of_isEffective_descentDatumOfBase b D hb
      (h U (fppfPullbackGroup hB G U b) V f hf Vij pr₁ pr₂ hVij Vijk s₁₂ s₂₃ hVijk q₁ q₂ q₃
        hq₁ hq₂ hq₃ (descentDatumOfBase b D hb) (fun _ => rfl))

end PrincipalHomogeneousSpaces

end AlgebraicGeometry.Space

end

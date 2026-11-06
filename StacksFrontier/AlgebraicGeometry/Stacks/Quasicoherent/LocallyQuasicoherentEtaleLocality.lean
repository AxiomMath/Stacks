module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Quasicoherence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.Localization
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LocallyQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SliceEquivalence.Sheaves
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence

/-!
# Quasi-coherence of the small-étale restriction is étale-local (Stacks 06WJ)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, `F` a presheaf of modules over
the structure sheaf of `𝒳` which is a sheaf for the étale topology, and `x` an object of `𝒳`
lying over the scheme `U`. The second clause of Stacks 06WJ asks that the restriction
`x^*F|_{U_ét}` of Stacks 06W1 be a quasi-coherent sheaf of modules on the small étale site of
`U`. This file proves that the clause only has to be checked after an étale covering of `x`: if
arrows `φ i : y i ⟶ x` of `𝒳` lie over étale morphisms of schemes which are jointly surjective,
and the clause holds at every `y i`, then it holds at `x`.

## Main definitions

* `AlgebraicGeometry.Stack.etaleChart`: the object of the small étale site of the scheme below
  `x` attached to an arrow into `x` lying over an étale morphism of schemes.
* `AlgebraicGeometry.Stack.chartPushforward`: restriction of a presheaf of modules along
  composition with that chart.

## Main results

* `AlgebraicGeometry.Stack.restrictModuleToSmallEtale_isSheaf`: the restriction of Stacks 06WJ
  of an étale sheaf of modules is a sheaf on the small étale site.
* `AlgebraicGeometry.Stack.isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover`:
  the second clause of Stacks 06WJ is étale-local on the object.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v w c d r n m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- Two restrictions of one presheaf of modules along isomorphic functors are isomorphic, as
soon as the two scalar morphisms agree after transport along the isomorphism. On sections the
isomorphism is the action of the presheaf on the component of the inverse isomorphism. -/
private noncomputable def moduleRestrictionIso
    {C : Type c} [Category.{d} C] {D : Type v} [Category.{w} D]
    {R : Dᵒᵖ ⥤ RingCat.{r}} {T : Cᵒᵖ ⥤ RingCat.{r}}
    {G H : C ⥤ D} (e : G ≅ H)
    (α : T ⟶ G.op ⋙ R) (β : T ⟶ H.op ⋙ R)
    (hα : ∀ X, α.app (op X) ≫ R.map (e.inv.app X).op = β.app (op X))
    (F : PresheafOfModules.{n} R) :
    (PresheafOfModules.pushforward α).obj F ≅
      (PresheafOfModules.pushforward β).obj F := by
  let η := Functor.isoWhiskerRight (NatIso.op e.symm) F.presheaf
  refine PresheafOfModules.isoMk (fun X => ?_) ?_
  · let L : ((PresheafOfModules.pushforward α).obj F).obj X →ₗ[T.obj X]
        ((PresheafOfModules.pushforward β).obj F).obj X :=
      { toFun := F.map (e.inv.app X.unop).op
        map_add' := map_add (F.presheaf.map (e.inv.app X.unop).op).hom
        map_smul' := fun a b => by
          let b' : F.obj (op (G.obj X.unop)) := b
          change F.map (e.inv.app X.unop).op (α.app X a • b') =
            β.app X a • F.map (e.inv.app X.unop).op b'
          rw [F.map_smul]
          exact congrArg (fun k => k • F.map (e.inv.app X.unop).op b')
            (congrArg (fun k => k.hom a) (hα X.unop)) }
    exact (LinearEquiv.ofBijective L
      (ConcreteCategory.bijective_of_isIso (η.hom.app X))).toModuleIso
  · intro X Y f
    ext a
    exact ConcreteCategory.congr_hom (η.hom.naturality f) a

/-- Cancelling the inverse of an isomorphism on the right of a factorization through it. -/
private theorem eq_of_comp_inv_eq {C : Type c} [Category.{d} C] {X Y Z : C}
    {f : X ⟶ Y} {g : X ⟶ Z} (i : Y ≅ Z) (hf : f = g ≫ i.inv) : f ≫ i.hom = g := by
  rw [hf, Category.assoc, i.inv_hom_id, Category.comp_id]

/-- Global functions turn a composite of morphisms of schemes into the opposite composite of
ring maps. -/
private theorem gamma_map_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    Scheme.Γ.map g.op ≫ Scheme.Γ.map f.op = Scheme.Γ.map (f ≫ g).op := by
  rw [← Functor.map_comp, ← op_comp]

variable {𝒳 : Type v} [Category.{w} 𝒳]

/-- The object of the small étale site of the scheme below `x` attached to an arrow `φ : z ⟶ x`
whose underlying morphism of schemes is étale: the morphism of schemes itself, read in the big
étale category. -/
@[implicit_reducible]
def etaleChart (p : 𝒳 ⥤ BigFppfOver B S hS) {z x : 𝒳} (φ : z ⟶ x)
    (hφ : Etale (B.inclusion.map (p.map φ).left)) :
    SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) :=
  ⟨Over.mk (smallEtaleBaseMorphism B E h S hS p φ),
    show Etale (E.inclusion.map (smallEtaleBaseMorphism B E h S hS p φ)) by
      simpa [smallEtaleBaseMorphism] using hφ⟩

/-- Restriction of a presheaf of modules along composition with the chart of an arrow `φ : z ⟶ x`,
from the small étale site of the scheme below `x` to that of the scheme below `z`. The scalars are
moved by the identity. -/
noncomputable abbrev chartPushforward (p : 𝒳 ⥤ BigFppfOver B S hS) {z x : 𝒳} (φ : z ⟶ x)
    (hφ : Etale (B.inclusion.map (p.map φ).left)) :
    PresheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj ⥤
      PresheafOfModules.{m} (SmallEtale.structureSheaf E (p.obj z).left.1
        (contains_base B E h S hS p z)).obj :=
  PresheafOfModules.pushforward
    (F := smallEtalePostcompose E (p.obj x).left.1 (contains_base B E h S hS p x)
      (etaleChart B E h S hS p φ hφ)) (eqToHom (by rfl))

/-- A family of objects of the small étale site of a scheme `X` whose image in schemes is an
étale covering of `X` generates a covering sieve for the small étale topology. -/
private theorem etaleFamily_mem (X : Scheme.{u}) (hX : E.Contains X)
    {W : SmallEtale E X hX} (D : PreZeroHypercover.{u + 1} W)
    (hD : (D.map (SmallEtale.toScheme E X hX)).presieve₀ ∈
      Scheme.etalePrecoverage ((SmallEtale.toScheme E X hX).obj W)) :
    Sieve.generate D.presieve₀ ∈ SmallEtale.topology E X hX W := by
  let H := SmallEtale.inclusion E X hX ⋙ Over.forget (E.obj X hX)
  have hDbig : IsEtaleCovering ⟨H.obj W, D.map H⟩ := hD
  obtain ⟨⟨T, R⟩, hR, hcomb⟩ := E.exists_covering_rep ⟨H.obj W, D.map H⟩ hDbig
  rcases hcomb with ⟨ht, hcomb⟩
  cases ht
  obtain ⟨β, hX', hf⟩ := hcomb.2
  have he (i : R.I₀) : Etale (E.inclusion.map (R.f i)) :=
    ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).1 hR.1).2 i
  let G : PreZeroHypercover.{u + 1} W :=
    { I₀ := R.I₀
      X i := ⟨Over.mk (R.f i ≫ W.obj.hom), by
        show Etale (E.inclusion.map (R.f i ≫ W.obj.hom))
        rw [E.inclusion.map_comp]
        let := he i
        infer_instance⟩
      f i := ObjectProperty.homMk (Over.homMk (R.f i)) }
  have hG : SmallEtale.IsCovering E X hX ⟨W, G⟩ := hR
  apply (SmallEtale.topology E X hX).superset_covering _
    ((SmallEtale.precoverage E X hX).generate_mem_toGrothendieck
      ((SmallEtale.mem_precoverage_iff E X hX).2 ⟨G, rfl, hG⟩))
  apply (Sieve.generate_le_iff _ _).2
  intro Y f hfmem
  obtain ⟨i⟩ := hfmem
  let g : G.X i ⟶ D.X (β i) := ObjectProperty.homMk
    (Over.homMk (eqToHom (hX' i)) (by
      show eqToHom (hX' i) ≫ (D.X (β i)).obj.hom = R.f i ≫ W.obj.hom
      rw [hf i]
      simp only [Category.assoc]
      congr 1
      exact (D.f (β i)).hom.w.symm))
  have hcomp : g ≫ D.f (β i) = G.f i := by
    ext
    exact congrArg (fun k => E.inclusion.map k) (hf i).symm
  rw [← hcomp]
  exact (Sieve.generate D.presieve₀).downward_closed
    (Sieve.le_generate _ _ _ (Presieve.ofArrows.mk _)) g

/-- For an arrow `φ : z ⟶ x` of `𝒳` lying over an étale morphism of schemes, the restriction at `x`
of a presheaf of modules, transported to the small étale site of the scheme below `z` along
composition with the chart of `φ`, is isomorphic to the restriction at `z`. -/
private noncomputable def restrictModulePostcomposeIso
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {z x : 𝒳} (φ : z ⟶ x)
    (hφ : Etale (B.inclusion.map (p.map φ).left))
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    (chartPushforward.{u, v, w, m} B E h S hS p φ hφ).obj
        (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
          (etaleTopology_le_topology B) F) ≅
      restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F := by
  let U := etaleChart B E h S hS p φ hφ
  let post := smallEtalePostcompose E (p.obj x).left.1 (contains_base B E h S hS p x) U
  let P := Over.post (X := z) (p ⋙ Over.forget (B.obj hS))
  let Q := Over.post (X := x) (p ⋙ Over.forget (B.obj hS))
  letI : P.IsEquivalence := isEquivalence_overPost B S hS p hp z
  letI : Q.IsEquivalence := isEquivalence_overPost B S hS p hp x
  let iz := smallEtaleInclusion B E h (p.obj z).left.1 (contains_base B E h S hS p z)
  let ix := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)
  let A := iz ⋙ P.inv ⋙ Over.map φ
  let C := post ⋙ ix ⋙ Q.inv
  have heq : iz ⋙ Over.map (p.map φ).left = post ⋙ ix := rfl
  let cmp : Over.map φ ⋙ Q ≅ P ⋙ Over.map (p.map φ).left :=
    NatIso.ofComponents (fun V => Over.isoMk (Iso.refl _) (by
      change 𝟙 _ ≫ (p.map V.hom).left ≫ (p.map φ).left =
        (p.map (V.hom ≫ φ)).left
      rw [p.map_comp, Over.comp_left, Category.id_comp]))
      (by intro V W a; ext; simp; rfl)
  let θ : A ⋙ Q ≅ iz ⋙ Over.map (p.map φ).left :=
    Functor.isoWhiskerLeft (iz ⋙ P.inv) cmp ≪≫
      Functor.isoWhiskerLeft iz
        (Functor.isoWhiskerRight P.asEquivalence.counitIso (Over.map (p.map φ).left))
  let ρ : C ⋙ Q ≅ post ⋙ ix :=
    Functor.isoWhiskerLeft (post ⋙ ix) Q.asEquivalence.counitIso
  let e : A ≅ C := Functor.fullyFaithfulCancelRight Q
    (θ ≪≫ eqToIso heq ≪≫ ρ.symm)
  let e' := Functor.isoWhiskerRight e.symm (Over.forget x)
  let α := Functor.whiskerLeft post.op (localStructurePresheafIso B E h S hS p hp x
    (etaleTopology B) (etaleTopology_le_topology B)).hom
  let β := (localStructurePresheafIso B E h S hS p hp z (etaleTopology B)
    (etaleTopology_le_topology B)).hom
  let γ : (SmallEtale.structureSheaf E (p.obj z).left.1
      (contains_base B E h S hS p z)).obj ⟶
      post.op ⋙ (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x)).obj := eqToHom (by rfl)
  refine moduleRestrictionIso
    (R := (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    e' (γ ≫ α) β ?_ F
  intro V
  have hgeo : (p.map (e.hom.app V).left).left ≫
      (Q.asEquivalence.counit.app (ix.obj (post.obj V))).left =
        (P.asEquivalence.counit.app (iz.obj V)).left := by
    have he' : Q.map (e.hom.app V) = θ.hom.app V ≫ (ρ.app V).inv := Q.map_preimage _
    have hcancel : Q.map (e.hom.app V) ≫ (ρ.app V).hom = θ.hom.app V :=
      eq_of_comp_inv_eq (ρ.app V) he'
    have hleft := congrArg (fun a => a.left) hcancel
    change (p.map (e.hom.app V).left).left ≫
        (Q.asEquivalence.counit.app (ix.obj (post.obj V))).left =
          𝟙 _ ≫ (P.asEquivalence.counit.app (iz.obj V)).left at hleft
    simpa only [Category.id_comp] using hleft
  have hmapcomp : B.inclusion.map (p.map (e.hom.app V).left).left ≫
      B.inclusion.map (Q.asEquivalence.counit.app (ix.obj (post.obj V))).left =
      B.inclusion.map (P.asEquivalence.counit.app (iz.obj V)).left :=
    (B.inclusion.map_comp _ _).symm.trans (congrArg B.inclusion.map hgeo)
  have hΓ := (gamma_map_comp (B.inclusion.map (p.map (e.hom.app V).left).left)
      (B.inclusion.map (Q.asEquivalence.counit.app (ix.obj (post.obj V))).left)).trans
    (congrArg (fun t => Scheme.Γ.map (Opposite.op t)) hmapcomp)
  ext s
  simp only [α, β]
  change (Scheme.Γ.map (B.inclusion.map (p.map (e.hom.app V).left).left).op).hom
      ((Scheme.Γ.map (B.inclusion.map
        (Q.objObjPreimageIso (ix.obj (post.obj V))).hom.left).op).hom s) =
    (Scheme.Γ.map (B.inclusion.map (P.objObjPreimageIso (iz.obj V)).hom.left).op).hom s
  exact congrArg (fun a => a.hom s) hΓ

/-- The restriction of Stacks 06WJ at an object `x` of a presheaf of modules which is a sheaf for
the étale topology is a sheaf on the small étale site of the scheme below `x`. -/
theorem restrictModuleToSmallEtale_isSheaf
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf) :
    Presheaf.IsSheaf (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
      (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F).presheaf := by
  let J := associatedTopology B S hS p (etaleTopology B)
  let Q := F.presheaf ⋙ forget AddCommGrpCat.{m}
  have hLift : Presheaf.IsSheaf J (Q ⋙ uliftFunctor.{max (u + 1) m, m}) :=
    Presheaf.isSheaf_comp_of_isSheaf J Q uliftFunctor
      (Presheaf.isSheaf_comp_of_isSheaf J F.presheaf (forget AddCommGrpCat) hF)
  have hsmall := restrictToSmallEtale_isSheaf B E h S hS p hp x
    (⟨Q ⋙ uliftFunctor.{max (u + 1) m, m}, hLift⟩ : Sheaf J (Type (max (u + 1) m)))
  rw [restrictModuleToSmallEtale_presheaf]
  exact Presheaf.isSheaf_of_isSheaf_comp _ _ (forget AddCommGrpCat.{m})
    (Presheaf.isSheaf_of_isSheaf_comp _ _ uliftFunctor.{max (u + 1) m, m} hsmall)

/-- The charts of a jointly surjective family of arrows into `x` lying over étale morphisms of
schemes cover the final object of the small étale site of the scheme below `x`. -/
private theorem coversTop_etaleChart (p : 𝒳 ⥤ BigFppfOver B S hS) (x : 𝒳)
    {I : Type (u + 1)} (y : I → 𝒳) (φ : ∀ i, y i ⟶ x)
    (hetale : ∀ i, Etale (B.inclusion.map (p.map (φ i)).left))
    (hcov : ∀ t : B.inclusion.obj (p.obj x).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (φ i)).left)) :
    (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x)).CoversTop
      (fun i => etaleChart B E h S hS p (φ i) (hetale i)) := by
  let hx := contains_base B E h S hS p x
  let V : I → SmallEtale E (p.obj x).left.1 hx :=
    fun i => etaleChart B E h S hS p (φ i) (hetale i)
  let W := SmallEtale.final E (p.obj x).left.1 hx
  let D : PreZeroHypercover.{u + 1} W :=
    { I₀ := I
      X := V
      f := fun i => ObjectProperty.homMk
        (Over.homMk (V i).obj.hom (by simp [W, SmallEtale.final])) }
  have hD : Sieve.generate D.presieve₀ ∈ SmallEtale.topology E (p.obj x).left.1 hx W :=
    etaleFamily_mem E (p.obj x).left.1 hx D
      ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).mpr ⟨hcov, fun i => (V i).property⟩)
  exact (GrothendieckTopology.coversTop_iff_of_isTerminal _ W
    (SmallEtale.finalIsTerminal E (p.obj x).left.1 hx) V).2
      ((SmallEtale.topology E (p.obj x).left.1 hx).superset_covering
        (Sieve.ofArrows_le_ofObjects D.X D.f) hD)

/-- Quasi-coherence of the restriction at the source of an arrow lying over an étale morphism of
schemes gives quasi-coherence of the restriction at the target over the chart of that arrow. -/
private theorem isQuasicoherentOnSite_over_etaleChart
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {z x : 𝒳} (φ : z ⟶ x)
    (hφ : Etale (B.inclusion.map (p.map φ).left))
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf)
    (hQC : (⟨restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
        (etaleTopology_le_topology B) F,
        restrictModuleToSmallEtale_isSheaf B E h S hS p hp z F hF⟩ :
      SheafOfModules (SmallEtale.structureSheaf E (p.obj z).left.1
        (contains_base B E h S hS p z))).IsQuasicoherentOnSite) :
    ((⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F,
        restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F hF⟩ :
      SheafOfModules (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x))).over
      (etaleChart B E h S hS p φ hφ)).IsQuasicoherentOnSite := by
  let hx := contains_base B E h S hS p x
  let U := etaleChart B E h S hS p φ hφ
  let R := SmallEtale.structureSheaf E (p.obj x).left.1 hx
  let M : SheafOfModules R :=
    ⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
      (etaleTopology_le_topology B) F,
      restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F hF⟩
  let eqv := smallEtaleEquivalenceOver E (p.obj x).left.1 hx U
  let N : SheafOfModules (SmallEtale.structureSheaf E U.obj.left.1 U.obj.left.property) :=
    ⟨restrictModuleToSmallEtale B E h S hS p hp z (etaleTopology B)
      (etaleTopology_le_topology B) F,
      restrictModuleToSmallEtale_isSheaf B E h S hS p hp z F hF⟩
  have eM : ((SheafOfModules.pushforward.{u}
      (𝟙 (Stacks.SheafOfModules.reindexRing
        (SmallEtale.topology E U.obj.left.1 U.obj.left.property) eqv (R.over U)))).obj
      (M.over U)).val ≅ N.val :=
    (PresheafOfModules.pushforwardComp (F := eqv.functor) (G := Over.forget U)
      (T := R.obj) (𝟙 _) (𝟙 _)).app M.val ≪≫ restrictModulePostcomposeIso B E h S hS p hp φ hφ F
  let eSheaf : (SheafOfModules.pushforward.{u}
      (𝟙 (Stacks.SheafOfModules.reindexRing
        (SmallEtale.topology E U.obj.left.1 U.obj.left.property) eqv (R.over U)))).obj
      (M.over U) ≅ N :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso eM
  exact Stacks.SheafOfModules.isQuasicoherentOnSite_of_reindex eqv (R.over U) (M.over U)
    (SheafOfModules.IsQuasicoherentOnSite.of_iso eSheaf.symm hQC)

/-- If arrows `φ i : y i ⟶ x` of `𝒳` lie over étale morphisms of schemes which are jointly
surjective onto the scheme below `x`, and the restriction to the small étale site is quasi-coherent
at every `y i`, then it is quasi-coherent at `x`. -/
theorem isQuasicoherentOnSite_restrictModuleToSmallEtale_of_etaleCover
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf)
    {I : Type (u + 1)} (y : I → 𝒳) (φ : ∀ i, y i ⟶ x)
    (hetale : ∀ i, Etale (B.inclusion.map (p.map (φ i)).left))
    (hcov : ∀ t : B.inclusion.obj (p.obj x).left,
      ∃ i, t ∈ Set.range (B.inclusion.map (p.map (φ i)).left))
    (hQC : ∀ i, (⟨restrictModuleToSmallEtale B E h S hS p hp (y i) (etaleTopology B)
        (etaleTopology_le_topology B) F,
        restrictModuleToSmallEtale_isSheaf B E h S hS p hp (y i) F hF⟩ :
      SheafOfModules (SmallEtale.structureSheaf E (p.obj (y i)).left.1
        (contains_base B E h S hS p (y i)))).IsQuasicoherentOnSite) :
    (⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
        (etaleTopology_le_topology B) F,
        restrictModuleToSmallEtale_isSheaf B E h S hS p hp x F hF⟩ :
      SheafOfModules (SmallEtale.structureSheaf E (p.obj x).left.1
        (contains_base B E h S hS p x))).IsQuasicoherentOnSite := by
  exact (Stacks.SheafOfModules.isQuasicoherentOnSite_iff_exists_cover_isQuasicoherentOnSite
    _).2 ⟨I, fun i => etaleChart B E h S hS p (φ i) (hetale i),
    coversTop_etaleChart B E h S hS p x y φ hetale hcov,
    fun i => isQuasicoherentOnSite_over_etaleChart B E h S hS p hp (φ i) (hetale i) F hF (hQC i)⟩

end AlgebraicGeometry.Stack

end

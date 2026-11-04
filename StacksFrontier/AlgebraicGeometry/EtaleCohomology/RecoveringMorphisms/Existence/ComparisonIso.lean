module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.Comparison
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.Existence.EtaleQuotientMap
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.RecoveringMorphisms.TargetStalkRingMapSet
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkPullbackGerm
public import StacksFrontier.Deformation.ToposThickening.Trivialization.AdjunctionForget

/-!
# The comparison `g⁻¹h_{V'} ⟶ h_{X ×_Y V'}` is an isomorphism

This is step (4) of the proof of Stacks 04I6, in the relative form needed for Stacks 04I7.  The
small étale site of `X` has enough points, so it suffices to check that the comparison is
bijective on the stalk at every point `p`.  At a point over `W_V` both stalks are solution sets
of the presented system, in the stalk ring `𝒪_{Y,q}` of the point `q` of `Y_étale` reconstructed
from `p` and in `𝒪_{X,p}`; the comparison is postcomposition with the stalk of `g^♯`, which is a
local homomorphism of strictly henselian local rings because `g` is locally ringed, and Stacks
04GX makes it bijective.  At a point not over `W_V` both stalks are empty.

## References

* [Stacks Project, Tag 04I7](https://stacks.math.columbia.edu/tag/04I7)
* [Stacks Project, Tag 04I6](https://stacks.math.columbia.edu/tag/04I6)
* [Stacks Project, Tag 04GX](https://stacks.math.columbia.edu/tag/04GX)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Limits

universe u

namespace AlgebraicGeometry

/-! ### Values of germs -/

section StalkValue

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (p : (SmallEtale.topology B S hS).Point.{u})

/-- The stalk of the structure sheaf of sets at `p`, read in the stalk ring. -/
def stalkValue :
    (p.sheafFiber (A := Type u)).obj (Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) →
      ↥(smallEtaleStalkRing B S hS p) := fun x =>
  (Stacks.commRingPresheafFiberIso p
    (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)).O.obj).hom.hom
    (Stacks.Sheaves.StalkTransport.ringStalkComparison p
      (smallEtaleSchemeRingSheaf B S hS) x)

/-- The stalk value of the germ at `x` of a section `s` of the structure sheaf is the image of `s`
under `smallEtaleGermHom`. -/
theorem stalkValue_germ (U : SmallEtale B S hS) (x : p.fiber.obj U)
    (s : ↥Γ((SmallEtale.toScheme B S hS).obj U, ⊤)) :
    stalkValue B S hS p
        (p.toPresheafFiber U x (Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)).obj s) =
      smallEtaleGermHom B S hS p U x s :=
  (congrArg (Stacks.commRingPresheafFiberIso p
    (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)).O.obj).hom.hom
    (Stacks.Sheaves.StalkTransport.ringStalkComparison_germ p
      (smallEtaleSchemeRingSheaf B S hS) U x s)).trans
    (Stacks.commRingPresheafFiberIso_hom_toPresheafFiber p
      (RingedSite.toRingedTopos (smallEtaleRingedSite B S hS)).O.obj U x s)

/-- The value at a germ of the stalk of a generalized element. -/
theorem stalkValue_map_germ {Z : Sheaf (SmallEtale.topology B S hS) (Type u)}
    (a : Z ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS)) (U : SmallEtale B S hS)
    (x : p.fiber.obj U) (z : Z.obj.obj (op U)) :
    stalkValue B S hS p ((p.sheafFiber (A := Type u)).map a (p.toPresheafFiber U x Z.obj z)) =
      smallEtaleGermHom B S hS p U x (a.hom.app (op U) z) :=
  (congrArg (stalkValue B S hS p)
    (ConcreteCategory.congr_hom (p.toPresheafFiber_naturality a.hom U x) z)).trans
    (stalkValue_germ B S hS p U x (a.hom.app (op U) z))

/-- The stalk at `p` of the sheaf represented by an open has at most one element. -/
instance subsingleton_sheafFiber_openSheaf (T : S.Opens) :
    Subsingleton ((p.sheafFiber (A := Type u)).obj (openSheaf B S hS T)) := by
  refine ⟨fun t₁ t₂ => ?_⟩
  obtain ⟨U, x, e₁, e₂, rfl, rfl⟩ :=
    p.toPresheafFiber_jointly_surjective₂ (P := (openSheaf B S hS T).obj) t₁ t₂
  rw [Subsingleton.elim e₁ e₂]

end StalkValue

/-! ### Stacks 04GX on solution sets -/

/-- **Stacks 04GX on the solutions of a system with coefficients.** -/
theorem bijective_solutions_comp {R A A' : Type u} [CommRing R] [CommRing A] [CommRing A']
    [HenselianLocalRing A] [HenselianLocalRing A'] [IsSepClosed (IsLocalRing.ResidueField A)]
    [IsSepClosed (IsLocalRing.ResidueField A')] (φ : A →+* A') (hφ : IsLocalHom φ) (c : R →+* A)
    {n : ℕ} (P : Fin n → MvPolynomial (Fin n) R)
    [Algebra.Etale A (MvPolynomial (Fin n) A ⧸
      Ideal.span (Set.range (fun j => MvPolynomial.map c (P j))))] :
    Function.Bijective (fun α : {α : Fin n → A // MvPolynomial.IsSolution P c α} =>
      (⟨fun i => φ (α.1 i), MvPolynomial.isSolution_comp c φ α.2⟩ :
        {β : Fin n → A' // MvPolynomial.IsSolution P (φ.comp c) β})) := by
  have h := bijOn_solutions_of_etale φ hφ n (fun j => MvPolynomial.map c (P j))
  refine ⟨fun α β hαβ => Subtype.ext (h.injOn α.2 β.2 (congrArg Subtype.val hαβ)), ?_⟩
  rintro ⟨β, hβ⟩
  have hβ' : β ∈ {s : Fin n → A' |
      ∀ i, MvPolynomial.eval s (MvPolynomial.map φ (MvPolynomial.map c (P i))) = 0} := by
    intro i
    rw [MvPolynomial.map_map]
    exact hβ i
  obtain ⟨α, hα, rfl⟩ := h.surjOn hβ'
  exact ⟨⟨α, hα⟩, rfl⟩

/-! ### Stalk coordinates of a relative solution presentation -/

/-- The `i`-th coordinate of the stalk solution of `ζ` is the stalk value of the image of `ζ` under
the `i`-th coordinate map `pres.coord i`. -/
theorem RelSolutionPresentation.stalkSolution_coe {B : BigEtaleSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} {T : S.Opens} {R : Type u} [CommRing R]
    {ψ : R →+* ↥Γ((SmallEtale.toScheme B S hS).obj (openObj B S hS T), ⊤)} {n : ℕ}
    {P : Fin n → MvPolynomial (Fin n) R} (pres : RelSolutionPresentation B S hS T ψ P)
    (p : (SmallEtale.topology B S hS).Point.{u}) {U₀ : SmallEtale B S hS} (x₀ : p.fiber.obj U₀)
    (k₀ : U₀ ⟶ openObj B S hS T) (ζ : (p.sheafFiber (A := Type u)).obj pres.sheaf) (i : Fin n) :
    (pres.stalkSolution p x₀ k₀ ζ).1 i = stalkValue B S hS p
      ((p.sheafFiber (A := Type u)).map
        (show pres.sheaf ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B S hS) from
          pres.coord i) ζ) := by
  obtain ⟨U, x, f, rfl⟩ := p.toPresheafFiber_jointly_surjective (P := pres.sheaf.obj) ζ
  rw [pres.stalkSolution_toPresheafFiber_coe p x₀ k₀ U x f i]
  exact (stalkValue_map_germ B S hS p (pres.coord i) U x f).symm

/-! ### The stalk of the transport of a generalized element -/

section Transport

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme}
  (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))

/-- **The stalk of `g⁻¹a ≫ g^♯` at `p` is the stalk of `a` at the reconstructed point, followed
by the stalk homomorphism of `g`.** -/
theorem stalkValue_transport (p : (SmallEtale.topology B X.obj X.property).Point.{u})
    {Z : Sheaf (SmallEtale.topology B Y.obj Y.property) (Type u)}
    (a : Z ⟶ Sheaf.ringSheaf (smallEtaleSchemeRingSheaf B Y.obj Y.property))
    (τ : ((g.targetSitePoint p).sheafFiber (A := Type u)).obj Z) :
    stalkValue B X.obj X.property p ((p.sheafFiber (A := Type u)).map
        (transportRingHom g (𝟙 _) a) ((g.targetSitePointIso p).hom.app Z τ)) =
      g.targetStalkRingMap p (stalkValue B Y.obj Y.property (g.targetSitePoint p)
        (((g.targetSitePoint p).sheafFiber (A := Type u)).map a τ)) := by
  have hfs : (sheafCompose (SmallEtale.topology B X.obj X.property) (forget RingCat.{u})).map
      g.toRingedToposModulesHom.fSharpInverseImage = g.fSharpSet :=
    RingedToposHom.fSharpInverseImage_forget_homEquiv g
  have e1 : (p.sheafFiber (A := Type u)).map (transportRingHom g (𝟙 _) a)
      ((g.targetSitePointIso p).hom.app Z τ) =
      (p.sheafFiber (A := Type u)).map g.fSharpSet ((p.sheafFiber (A := Type u)).map
        (g.toToposHom.inverseImage.map a) ((g.targetSitePointIso p).hom.app Z τ)) :=
    (congrArg (fun m => (p.sheafFiber (A := Type u)).map m ((g.targetSitePointIso p).hom.app Z τ))
      (Category.id_comp (g.toToposHom.inverseImage.map a ≫ g.fSharpSet))).trans
      (Functor.map_comp_apply _ _ _ _)
  have e2 : (p.sheafFiber (A := Type u)).map (g.toToposHom.inverseImage.map a)
      ((g.targetSitePointIso p).hom.app Z τ) =
      (g.targetSitePointIso p).hom.app _
        (((g.targetSitePoint p).sheafFiber (A := Type u)).map a τ) :=
    (ConcreteCategory.congr_hom ((g.targetSitePointIso p).hom.naturality a) τ).symm
  rw [e1, e2, ← hfs]
  exact (g.targetStalkRingMap_ringStalkComparison p
    (((g.targetSitePoint p).sheafFiber (A := Type u)).map a τ)).symm

end Transport

/-! ### The comparison is bijective on stalks -/

section Iso

variable {B : BigEtaleSite.{u}} {X Y : B.Scheme}
  (g : RingedToposHom (RingedSite.toRingedTopos (smallEtaleRingedSite B X.obj X.property))
      (RingedSite.toRingedTopos (smallEtaleRingedSite B Y.obj Y.property)))
  (hg : g.IsLocallyRinged) (V : Y.obj.affineOpens)
  {V' : SmallEtale B Y.obj Y.property} [IsAffine ((SmallEtale.toScheme B Y.obj Y.property).obj V')]
  (k : V' ⟶ openObj B Y.obj Y.property V) {n : ℕ}
  (P : Fin n → MvPolynomial (Fin n)
    Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤))
  (pres : Stacks.EtaleCohomology.StandardPresentationOver
    ((SmallEtale.toScheme B Y.obj Y.property).obj V')
    ((SmallEtale.toScheme B Y.obj Y.property).map k) P)

/-- The coefficients of the source row at a point over `W_V` are those of the target row at the
reconstructed point, pushed along the stalk homomorphism of `g`. -/
theorem germHom_comp_relCoeff_inverseImageOpen
    (p : (SmallEtale.topology B X.obj X.property).Point.{u}) {U₀ : SmallEtale B X.obj X.property}
    (x₀ : p.fiber.obj U₀) (k₀ : U₀ ⟶ openObj B X.obj X.property (inverseImageOpen B X Y g V))
    {V₀ : SmallEtale B Y.obj Y.property} (y₀ : (g.targetSitePoint p).fiber.obj V₀)
    (l₀ : V₀ ⟶ openObj B Y.obj Y.property V)
    (hξ : (g.targetSitePoint p).toPresheafFiber V₀ y₀ (openSheaf B Y.obj Y.property V).obj l₀ =
      (g.targetSitePointIso p).inv.app (openSheaf B Y.obj Y.property V)
        ((p.sheafFiber (A := Type u)).map (inverseImageOpenIso g V).inv
          (p.toPresheafFiber U₀ x₀
            (openSheaf B X.obj X.property (inverseImageOpen B X Y g V)).obj k₀))) :
    (smallEtaleGermHom B X.obj X.property p U₀ x₀).comp
        (relCoeff B X.obj X.property (inverseImageOpen B X Y g V) (openRingHomObj g V) k₀) =
      (g.targetStalkRingMap p).comp ((smallEtaleGermHom B Y.obj Y.property (g.targetSitePoint p)
        V₀ y₀).comp (relCoeff B Y.obj Y.property V (RingHom.id _) l₀)) := by
  let W := inverseImageOpen B X Y g V
  let e := inverseImageOpenIso g V
  let q := g.targetSitePoint p
  let T : smallEtaleStalkRing B Y.obj Y.property q →+* smallEtaleStalkRing B X.obj X.property p :=
    g.targetStalkRingMap p
  let w : (p.sheafFiber (A := Type u)).obj (openSheaf B X.obj X.property W) :=
    p.toPresheafFiber U₀ x₀ (openSheaf B X.obj X.property W).obj k₀
  let ξ := (g.targetSitePointIso p).inv.app (openSheaf B Y.obj Y.property V)
    ((p.sheafFiber (A := Type u)).map e.inv w)
  refine RingHom.ext fun b => ?_
  let yb := (smallEtaleSectionRingEquiv B Y.obj Y.property (openObj B Y.obj Y.property V)).symm b
  let φb := (smallEtaleSectionRingEquiv B X.obj X.property (openObj B X.obj X.property W)).symm
    (openRingHomObj g V b)
  calc _ = stalkValue B X.obj X.property p ((p.sheafFiber (A := Type u)).map φb w) :=
        (congrArg (smallEtaleGermHom B X.obj X.property p U₀ x₀)
          (smallEtaleSectionRingEquiv_symm_hom_app B X.obj X.property _ _ (op U₀) k₀)).symm.trans
          (stalkValue_map_germ B X.obj X.property p φb U₀ x₀ k₀).symm
    _ = stalkValue B X.obj X.property p ((p.sheafFiber (A := Type u)).map
          (e.inv ≫ transportRingHom g (𝟙 _) yb) w) :=
        congrArg (fun m => stalkValue B X.obj X.property p ((p.sheafFiber (A := Type u)).map m w))
          ((smallEtaleSectionRingEquiv_symm_openRingHomObj g V b).trans
            (congrArg (e.inv ≫ ·) (Category.id_comp _).symm))
    _ = stalkValue B X.obj X.property p ((p.sheafFiber (A := Type u)).map
          (transportRingHom g (𝟙 _) yb) ((p.sheafFiber (A := Type u)).map e.inv w)) :=
        congrArg (stalkValue B X.obj X.property p)
          (ConcreteCategory.congr_hom ((p.sheafFiber (A := Type u)).map_comp e.inv
            (transportRingHom g (𝟙 _) yb)) w)
    _ = stalkValue B X.obj X.property p ((p.sheafFiber (A := Type u)).map
          (transportRingHom g (𝟙 _) yb) ((g.targetSitePointIso p).hom.app _ ξ)) :=
        congrArg (fun z => stalkValue B X.obj X.property p
          ((p.sheafFiber (A := Type u)).map (transportRingHom g (𝟙 _) yb) z))
          (ConcreteCategory.congr_hom
            ((g.targetSitePointIso p).inv_hom_id_app (openSheaf B Y.obj Y.property V)) _).symm
    _ = T (stalkValue B Y.obj Y.property q ((q.sheafFiber (A := Type u)).map yb ξ)) :=
        stalkValue_transport g p yb ξ
    _ = T (stalkValue B Y.obj Y.property q ((q.sheafFiber (A := Type u)).map yb
          (q.toPresheafFiber V₀ y₀ (openSheaf B Y.obj Y.property V).obj l₀))) :=
        congrArg (fun z => T (stalkValue B Y.obj Y.property q
          ((q.sheafFiber (A := Type u)).map yb z))) hξ.symm
    _ = T (smallEtaleGermHom B Y.obj Y.property q V₀ y₀ (yb.hom.app (op V₀) l₀)) :=
        congrArg T (stalkValue_map_germ B Y.obj Y.property q yb V₀ y₀ l₀)
    _ = _ :=
        congrArg (fun z => T (smallEtaleGermHom B Y.obj Y.property q V₀ y₀ z))
          (smallEtaleSectionRingEquiv_symm_hom_app B Y.obj Y.property _ b (op V₀) l₀)

/-- The stalk solution of the image under the comparison of a point of the target row is the
target stalk solution pushed along the stalk homomorphism of `g`. -/
theorem stalkSolution_comparison (p : (SmallEtale.topology B X.obj X.property).Point.{u})
    {U₀ : SmallEtale B X.obj X.property} (x₀ : p.fiber.obj U₀)
    (k₀ : U₀ ⟶ openObj B X.obj X.property (inverseImageOpen B X Y g V))
    {V₀ : SmallEtale B Y.obj Y.property} (y₀ : (g.targetSitePoint p).fiber.obj V₀)
    (l₀ : V₀ ⟶ openObj B Y.obj Y.property V)
    (τ : ((g.targetSitePoint p).sheafFiber (A := Type u)).obj
      (targetRelPresentation V k P pres).sheaf) :
    ((sourceRelPresentation g V k P pres hg).stalkSolution p x₀ k₀
        ((p.sheafFiber (A := Type u)).map (comparison g hg V k P pres)
          ((g.targetSitePointIso p).hom.app _ τ))).1 =
      fun i => g.targetStalkRingMap p
        (((targetRelPresentation V k P pres).stalkSolution (g.targetSitePoint p) y₀ l₀ τ).1 i) := by
  let presX := sourceRelPresentation g V k P pres hg
  let presY := targetRelPresentation V k P pres
  let q := g.targetSitePoint p
  let T : smallEtaleStalkRing B Y.obj Y.property q →+* smallEtaleStalkRing B X.obj X.property p :=
    g.targetStalkRingMap p
  funext i
  refine (RelSolutionPresentation.stalkSolution_coe presX p x₀ k₀ _ i).trans
    (Eq.trans ?_ (congrArg T (RelSolutionPresentation.stalkSolution_coe presY q y₀ l₀ τ i)).symm)
  let σ := (g.targetSitePointIso p).hom.app ((smallEtaleYoneda B Y.obj Y.property).obj V') τ
  calc stalkValue B X.obj X.property p ((p.sheafFiber (A := Type u)).map
        (sourceCoord g hg V k P pres i)
        ((p.sheafFiber (A := Type u)).map (comparison g hg V k P pres) σ))
      = stalkValue B X.obj X.property p ((p.sheafFiber (A := Type u)).map
        (comparison g hg V k P pres ≫ sourceCoord g hg V k P pres i) σ) :=
        congrArg (stalkValue B X.obj X.property p)
          (ConcreteCategory.congr_hom ((p.sheafFiber (A := Type u)).map_comp _ _) σ).symm
    _ = stalkValue B X.obj X.property p ((p.sheafFiber (A := Type u)).map
        (transportRingHom g (𝟙 _) (targetCoord V k P pres i)) σ) :=
        congrArg (fun m => stalkValue B X.obj X.property p ((p.sheafFiber (A := Type u)).map m σ))
          (comparison_comp_sourceCoord g hg V k P pres i)
    _ = T (stalkValue B Y.obj Y.property q ((q.sheafFiber (A := Type u)).map
        (targetCoord V k P pres i) τ)) :=
        stalkValue_transport g p (targetCoord V k P pres i) τ

/-- **The comparison is bijective on the stalk at every point.** -/
theorem bijective_sheafFiber_comparison
    [Algebra.Etale Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤)
      (MvPolynomial (Fin n) Γ((SmallEtale.toScheme B Y.obj Y.property).obj
        (openObj B Y.obj Y.property V), ⊤) ⧸ Ideal.span (Set.range P))]
    (p : (SmallEtale.topology B X.obj X.property).Point.{u}) :
    Function.Bijective ((p.sheafFiber (A := Type u)).map (comparison g hg V k P pres)) := by
  let presX := sourceRelPresentation g V k P pres hg
  let presY := targetRelPresentation V k P pres
  let W := inverseImageOpen B X Y g V
  let q := g.targetSitePoint p
  by_cases hW : Nonempty ((p.sheafFiber (A := Type u)).obj (openSheaf B X.obj X.property W))
  swap
  · have h₁ : IsEmpty ((p.sheafFiber (A := Type u)).obj (g.toToposHom.inverseImage.obj
        ((smallEtaleYoneda B Y.obj Y.property).obj V'))) :=
      ⟨fun σ => hW ⟨(p.sheafFiber (A := Type u)).map (comparisonOver g V k) σ⟩⟩
    have h₂ : IsEmpty ((p.sheafFiber (A := Type u)).obj presX.sheaf) :=
      ⟨fun ζ => hW ⟨(p.sheafFiber (A := Type u)).map presX.toOpenSheaf ζ⟩⟩
    exact ⟨fun a => h₁.elim a, fun b => h₂.elim b⟩
  obtain ⟨w⟩ := hW
  obtain ⟨U₀, x₀, k₀', rfl⟩ :=
    p.toPresheafFiber_jointly_surjective (P := (openSheaf B X.obj X.property W).obj) w
  let k₀ : U₀ ⟶ openObj B X.obj X.property W := k₀'
  let ξ := (g.targetSitePointIso p).inv.app (openSheaf B Y.obj Y.property V)
    ((p.sheafFiber (A := Type u)).map (inverseImageOpenIso g V).inv
      (p.toPresheafFiber U₀ x₀ (openSheaf B X.obj X.property W).obj k₀'))
  obtain ⟨V₀, y₀, l₀', hξ⟩ :=
    q.toPresheafFiber_jointly_surjective (P := (openSheaf B Y.obj Y.property V).obj) ξ
  let l₀ : V₀ ⟶ openObj B Y.obj Y.property V := l₀'
  let T : smallEtaleStalkRing B Y.obj Y.property q →+* smallEtaleStalkRing B X.obj X.property p :=
    g.targetStalkRingMap p
  let cq := (smallEtaleGermHom B Y.obj Y.property q V₀ y₀).comp
    (relCoeff B Y.obj Y.property V (RingHom.id _) l₀)
  have hcoef := germHom_comp_relCoeff_inverseImageOpen g V p x₀ k₀ y₀ l₀ hξ
  have hsq := stalkSolution_comparison g hg V k P pres p x₀ k₀ y₀ l₀
  have := MvPolynomial.etale_quotient_map cq P
  have hM := bijective_solutions_comp T (g.isLocalHom_targetStalkRingMap hg p) cq P
  have hSY := presY.bijective_stalkSolution q y₀ l₀
  have hι : Function.Bijective ((g.targetSitePointIso p).hom.app presY.sheaf) :=
    (isIso_iff_bijective _).1 inferInstance
  refine ⟨fun a₁ a₂ h => ?_, fun ζ => ?_⟩
  · obtain ⟨τ₁, rfl⟩ := hι.2 a₁
    obtain ⟨τ₂, rfl⟩ := hι.2 a₂
    refine congrArg _ (hSY.1 (hM.1 (Subtype.ext ?_)))
    exact (hsq τ₁).symm.trans
      ((congrArg (fun z => (presX.stalkSolution p x₀ k₀ z).1) h).trans (hsq τ₂))
  · obtain ⟨α, hα⟩ := hM.2 ⟨(presX.stalkSolution p x₀ k₀ ζ).1,
      (congrArg (fun c => MvPolynomial.IsSolution P c (presX.stalkSolution p x₀ k₀ ζ).1) hcoef).mp
        (presX.stalkSolution p x₀ k₀ ζ).2⟩
    obtain ⟨τ, rfl⟩ := hSY.2 α
    refine ⟨(g.targetSitePointIso p).hom.app _ τ, (presX.bijective_stalkSolution p x₀ k₀).1
      (Subtype.ext ?_)⟩
    exact (hsq τ).trans (congrArg Subtype.val hα)

/-- **The comparison `g⁻¹h_{V'} ⟶ h_{X ×_Y V'}` is an isomorphism.** -/
theorem isIso_comparison
    [Algebra.Etale Γ((SmallEtale.toScheme B Y.obj Y.property).obj (openObj B Y.obj Y.property V), ⊤)
      (MvPolynomial (Fin n) Γ((SmallEtale.toScheme B Y.obj Y.property).obj
        (openObj B Y.obj Y.property V), ⊤) ⧸ Ideal.span (Set.range P))] :
    IsIso (comparison g hg V k P pres) := by
  rw [(isConservativeFamilyOfPoints_geometricSitePoints B X.obj
    X.property).jointlyReflectIsomorphisms_type.isIso_iff]
  intro Φ
  rw [isIso_iff_bijective]
  exact bijective_sheafFiber_comparison g hg V k P pres Φ.obj

end Iso

end AlgebraicGeometry

end

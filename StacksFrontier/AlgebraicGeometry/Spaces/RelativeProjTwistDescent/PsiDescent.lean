module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PsiTransition
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.PointComparisonQuasicoherent
import all StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationSchemeDescent
import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentColimits

/-!
# The coherence of the chart identifications of `ψ` in Stacks 084D

In Situation 0849 the source `π^*𝒜_n` of the homomorphism `ψ` of Stacks 084D is identified on
the atlas `c : P_U ⟶ P` with the module attached to `π_U^*(u^*𝒜)_n`
(`AlgebraicGeometry.Space.RelativeProjSituation.psiChartSourceIso`), through the composition
comparisons of Stacks 03LU, transports along equal morphisms, and the identifications
`g^*(M^a) ≅ (g^*M)^a` of Stacks 03DX (2).  This file proves the coherences of these comparisons
along the two projections of the presentation that the compatibility of `ψ` with the descent data
reduces to, at free variables.

## Main results

* `AlgebraicGeometry.Space.modulePullback_map_inv_comp_pullbackTransport_comp_eq`: the
  contraction `y^*f_U^*p^* ≅ f_R^*k^*p^*` along a square `y ≫ f_U = f_R ≫ k`, read between
  `y^*(f_U ≫ p)^*` and `f_R^*(k ≫ p)^*`, is a transport.
* `AlgebraicGeometry.Space.modulePullback_map_comp_modulePullbackCompIso_eq_of_squares`: **the
  chart coherence of Stacks 03LU**, the identification `y^*c^*π^*M ≅ f_R^*p_R^*M` through
  `f_U^*p_U^*M` and `f_R^*k^*p_U^*M` is the contraction along `(y ≫ c) ≫ π = f_R ≫ p_R`.
* `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_hom_comp_map_eqToHom`: the
  identifications `g^*(M^a) ≅ (g^*M)^a` along equal morphisms of the site.
* `modulePullbackCompIso_trans_eqToIso_hom_app_comp_pullbackTransport_comp_inv_app` (in
  `AlgebraicGeometry.Space`): the contractions of Stacks 03LU transported to given composites,
  along a commutative square.
* `modulePullback_map_modulePullbackRepresentedQuasicoherentIso_comp_chain` (in
  `AlgebraicGeometry.Space`): the identifications `g^*(M^a) ≅ (g^*M)^a` along a commutative
  square of the site, followed by the module attached to a chain on schemes, are the contraction
  of Stacks 03LU along the square followed by the identifications along the other side.

## Implementation notes

Every transport `AlgebraicGeometry.Space.pullbackTransport` is written so that the objects on
either side of it are spelled exactly as its own source and target (the contractions of Stacks 03LU
are written with the nested spelling `f^*(g^*M)`, the composites `f ≫ g ≫ h` are identified with
`(f ≫ g) ≫ h` by a transport along `Category.assoc`), and every proof of an equality of morphisms
appearing inside a transport is a hypothesis.  Comparing two composites containing a transport
whose intermediate objects are spelled differently (`(g^* ⋙ f^*).obj M` against `f^*(g^*M)`, or
`f ≫ (g ≫ h)` against `(f ≫ g) ≫ h`) unfolds the transport and does not terminate in the
kernel in reasonable time.  For the same reason the two chart coherences are stated with named
binary composites (`CategoryTheory.comp₂`), which the kernel compares factor by factor.

The composite of two morphisms represented by morphisms of the site is formed, in
`AlgebraicGeometry.Space.representedSpaceMap_comp`, in the full subcategory of presheaves (the
type of the represented morphisms), while the contraction of Stacks 03LU forms it in
`AlgebraicGeometry.AlgebraicSpaces`.  The two composites are definitionally equal, but two
composites of modules whose intermediate objects are inverse images along the two spellings are
not compared in reasonable time.  The equalities of represented composites are therefore stated
with `CategoryStruct.comp (obj := AlgebraicGeometry.AlgebraicSpaces B S hS)`, and the lemmas at
free morphisms take the composite of `representedSpaceMap_comp` in the full subcategory.

## References

* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public noncomputable section

universe u m

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Space

section Coherence

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The transport of `M` along `g = g'`, pulled back along `f`, between the contractions of
Stacks 03LU along `f ≫ g` and `f ≫ g'`, is the transport along `f ≫ g = f ≫ g'`. -/
theorem modulePullback_map_pullbackTransport_comp_modulePullbackCompIso_hom
    {T Y X : AlgebraicSpaces B S hS} (f : T ⟶ Y) {g g' : Y ⟶ X} (h : g = g')
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS f).map (pullbackTransport M h) ≫
        (modulePullbackCompIso B S hS f g').hom.app M =
      (modulePullbackCompIso B S hS f g).hom.app M ≫
        pullbackTransport M (congrArg (f ≫ ·) h : f ≫ g = f ≫ g') := by
  subst h
  simp [pullbackTransport]

/-- The inverse contraction along `f ≫ g`, followed by the pullback along `f` of the transport of
`M` along `g = g'`, is the transport along `f ≫ g = f ≫ g'` followed by the inverse contraction
along `f ≫ g'`.  The intermediate object is spelled `f^*(g^*M)`, as the source of the pulled back
transport. -/
theorem modulePullbackCompIso_inv_app_comp_modulePullback_map_pullbackTransport
    {T Y X : AlgebraicSpaces B S hS} (f : T ⟶ Y) {g g' : Y ⟶ X} (h : g = g')
    (M : Modules.{u, u} B S hS X.1 X.2) :
    CategoryStruct.comp (Y := (modulePullback B S hS f).obj ((modulePullback B S hS g).obj M))
        ((modulePullbackCompIso B S hS f g).inv.app M)
        ((modulePullback B S hS f).map (pullbackTransport M h)) =
      pullbackTransport M (congrArg (f ≫ ·) h : f ≫ g = f ≫ g') ≫
        (modulePullbackCompIso B S hS f g').inv.app M := by
  subst h
  simp [pullbackTransport]

/-- The associativity coherence of the comparisons of Stacks 03LU, with the two composites
`f ≫ (g ≫ h)` and `(f ≫ g) ≫ h` identified by the transport along `Category.assoc`. -/
theorem modulePullback_map_modulePullbackCompIso_hom_comp_eq_comp_pullbackTransport
    {W X Y Z : AlgebraicSpaces B S hS} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (modulePullback B S hS f).map ((modulePullbackCompIso B S hS g h).hom.app M) ≫
        (modulePullbackCompIso B S hS f (g ≫ h)).hom.app M =
      (modulePullbackCompIso B S hS f g).hom.app ((modulePullback B S hS h).obj M) ≫
        (modulePullbackCompIso B S hS (f ≫ g) h).hom.app M ≫
          pullbackTransport M (Category.assoc f g h) := by
  have hid : pullbackTransport M (Category.assoc f g h) = 𝟙 _ := rfl
  rw [hid, Category.comp_id]
  exact (modulePullbackCompIsoAssoc B S hS).hom_app f g h M

/-- The abstract shape of
`AlgebraicGeometry.Space.modulePullback_map_inv_comp_pullbackTransport_comp_eq`, at variables. -/
private theorem comp_comp_eq_of_contractions {C : Type*} [Category C]
    {O1 O2 O3 O4 O5 O6 O7 O8 O7a O8a : C} (m1 : O1 ⟶ O2) (c1 : O2 ⟶ O3) (t : O3 ⟶ O4)
    (c2 : O4 ⟶ O5) (c3 : O5 ⟶ O6) (d1 : O1 ⟶ O7) (t' : O7 ⟶ O8) (d3 : O8 ⟶ O6)
    (m1' : O2 ⟶ O1) (e2 : O3 ⟶ O7a) (as : O7a ⟶ O7) (e2i : O7a ⟶ O3) (asi : O7 ⟶ O7a)
    (t3 : O7a ⟶ O8a) (e3 : O4 ⟶ O8a) (bs : O8a ⟶ O8) (c2i : O5 ⟶ O4) (D : O6 ⟶ O8)
    (hid : m1 ≫ m1' = 𝟙 _) (hA0 : m1' ≫ d1 = c1 ≫ e2 ≫ as) (has : as ≫ asi = 𝟙 _)
    (he2 : e2 ≫ e2i = 𝟙 _) (ht : e2i ≫ t ≫ e3 = t3) (hB0 : c3 ≫ D = c2i ≫ e3 ≫ bs)
    (hc2 : c2 ≫ c2i = 𝟙 _) (hD : D ≫ d3 = 𝟙 _) (htt : asi ≫ t3 ≫ bs = t') :
    m1 ≫ c1 ≫ t ≫ c2 ≫ c3 = d1 ≫ t' ≫ d3 := by
  subst ht htt
  have k1 : m1 ≫ c1 = d1 ≫ asi ≫ e2i := by
    calc m1 ≫ c1 = (m1 ≫ c1 ≫ e2 ≫ as) ≫ asi ≫ e2i := by
          simp only [Category.assoc, reassoc_of% has, he2, Category.comp_id]
      _ = d1 ≫ asi ≫ e2i := by rw [← hA0, reassoc_of% hid]
  have k2 : c2 ≫ c3 = e3 ≫ bs ≫ d3 := by
    calc c2 ≫ c3 = c2 ≫ (c3 ≫ D) ≫ d3 := by rw [Category.assoc, hD, Category.comp_id]
      _ = e3 ≫ bs ≫ d3 := by rw [hB0]; simp only [Category.assoc, reassoc_of% hc2]
  rw [reassoc_of% k1, k2]
  simp only [Category.assoc]

/-- **The coherence of the contractions of Stacks 03LU along two composable squares**: for
`y ≫ f_U = f_R ≫ k`, the contraction `y^*f_U^*p^* ≅ f_R^*k^*p^*` along the square, read between
`y^*(f_U ≫ p)^*` and `f_R^*(k ≫ p)^*`, is the transport of `M` along
`y ≫ f_U ≫ p = f_R ≫ k ≫ p` between the contractions. -/
theorem modulePullback_map_inv_comp_pullbackTransport_comp_eq
    {W V U R X : AlgebraicSpaces B S hS} (y : W ⟶ V) (fU : V ⟶ U) (pu : U ⟶ X) (fR : W ⟶ R)
    (k : R ⟶ U) (e : y ≫ fU = fR ≫ k) (e' : y ≫ fU ≫ pu = fR ≫ k ≫ pu)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS y).map ((modulePullbackCompIso B S hS fU pu).inv.app M) ≫
        (modulePullbackCompIso B S hS y fU).hom.app ((modulePullback B S hS pu).obj M) ≫
          pullbackTransport ((modulePullback B S hS pu).obj M) e ≫
            (modulePullbackCompIso B S hS fR k).inv.app ((modulePullback B S hS pu).obj M) ≫
              (modulePullback B S hS fR).map ((modulePullbackCompIso B S hS k pu).hom.app M) =
      (modulePullbackCompIso B S hS y (fU ≫ pu)).hom.app M ≫
        pullbackTransport M e' ≫
          (modulePullbackCompIso B S hS fR (k ≫ pu)).inv.app M := by
  have hid : (modulePullback B S hS y).map ((modulePullbackCompIso B S hS fU pu).inv.app M) ≫
      (modulePullback B S hS y).map ((modulePullbackCompIso B S hS fU pu).hom.app M) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app]
    exact (modulePullback B S hS y).map_id _
  have has : pullbackTransport M (Category.assoc y fU pu) ≫
      pullbackTransport M (Category.assoc y fU pu).symm = 𝟙 _ := by
    simp only [pullbackTransport, eqToIso.hom, eqToHom_refl, Category.comp_id]
  have htt : pullbackTransport M (Category.assoc y fU pu).symm ≫
      pullbackTransport M (congrArg (· ≫ pu) e : (y ≫ fU) ≫ pu = (fR ≫ k) ≫ pu) ≫
        pullbackTransport M (Category.assoc fR k pu) =
      pullbackTransport M e' :=
    pullbackTransport_comp₃ B S hS M _ _ _ _
  exact comp_comp_eq_of_contractions
    (m1 := (modulePullback B S hS y).map ((modulePullbackCompIso B S hS fU pu).inv.app M))
    (c1 := (modulePullbackCompIso B S hS y fU).hom.app ((modulePullback B S hS pu).obj M))
    (t := pullbackTransport ((modulePullback B S hS pu).obj M) e)
    (c2 := (modulePullbackCompIso B S hS fR k).inv.app ((modulePullback B S hS pu).obj M))
    (c3 := (modulePullback B S hS fR).map ((modulePullbackCompIso B S hS k pu).hom.app M))
    (d1 := (modulePullbackCompIso B S hS y (fU ≫ pu)).hom.app M)
    (t' := pullbackTransport M e')
    (d3 := (modulePullbackCompIso B S hS fR (k ≫ pu)).inv.app M)
    (m1' := (modulePullback B S hS y).map ((modulePullbackCompIso B S hS fU pu).hom.app M))
    (e2 := (modulePullbackCompIso B S hS (y ≫ fU) pu).hom.app M)
    (as := pullbackTransport M (Category.assoc y fU pu))
    (e2i := (modulePullbackCompIso B S hS (y ≫ fU) pu).inv.app M)
    (asi := pullbackTransport M (Category.assoc y fU pu).symm)
    (t3 := pullbackTransport M (congrArg (· ≫ pu) e : (y ≫ fU) ≫ pu = (fR ≫ k) ≫ pu))
    (e3 := (modulePullbackCompIso B S hS (fR ≫ k) pu).hom.app M)
    (bs := pullbackTransport M (Category.assoc fR k pu))
    (c2i := (modulePullbackCompIso B S hS fR k).hom.app ((modulePullback B S hS pu).obj M))
    (D := (modulePullbackCompIso B S hS fR (k ≫ pu)).hom.app M)
    hid (modulePullback_map_modulePullbackCompIso_hom_comp_eq_comp_pullbackTransport y fU pu M)
    has (Iso.hom_inv_id_app _ _) (modulePullbackCompIso_inv_comp_pullbackTransport_comp_hom pu e M)
    (modulePullback_map_modulePullbackCompIso_hom_comp_eq_comp_pullbackTransport fR k pu M)
    (Iso.inv_hom_id_app _ _) (Iso.hom_inv_id_app _ _) htt

/-- The abstract shape of
`AlgebraicGeometry.Space.modulePullback_map_comp_modulePullbackCompIso_eq_of_squares`, at
variables. -/
private theorem comp_eq_of_chart_contractions {C : Type*} [Category C]
    {P0 P1 P2 O2 O3 O4 O5 O6 P7 R1 Q1' Q4 Q1 Q2 Q3 : C}
    (x1 : P0 ⟶ P1) (x2 : P1 ⟶ P2) (m1 : P2 ⟶ O2) (c1 : O2 ⟶ O3) (t : O3 ⟶ O4) (c2 : O4 ⟶ O5)
    (c3 : O5 ⟶ O6) (x3 : O6 ⟶ P7)
    (g1 : P0 ⟶ R1) (g2 : R1 ⟶ Q1') (tt : Q1' ⟶ Q4) (d4 : Q4 ⟶ P7)
    (d1 : P2 ⟶ Q2) (t'' : Q2 ⟶ Q3) (d3 : Q3 ⟶ O6) (e1 : P1 ⟶ Q1) (t1 : Q1 ⟶ Q2)
    (as : Q1' ⟶ Q1) (t2 : Q3 ⟶ Q4)
    (hcoh : m1 ≫ c1 ≫ t ≫ c2 ≫ c3 = d1 ≫ t'' ≫ d3)
    (hn1 : x2 ≫ d1 = e1 ≫ t1) (ha1 : x1 ≫ e1 = g1 ≫ g2 ≫ as)
    (hn2 : d3 ≫ x3 = t2 ≫ d4) (htt : as ≫ t1 ≫ t'' ≫ t2 = tt) :
    comp₂ x1 (comp₂ x2 (comp₂ m1 (comp₂ c1 (comp₂ t (comp₂ c2 (comp₂ c3 x3)))))) =
      comp₂ g1 (comp₂ g2 (comp₂ tt d4)) := by
  simp only [comp₂_eq]
  subst htt
  rw [reassoc_of% hcoh, reassoc_of% hn1, reassoc_of% ha1, hn2]
  simp only [Category.assoc]

/-- **The chart coherence of Stacks 03LU**: for `c ≫ π = f_U ≫ p_U`, `y ≫ f_U = f_R ≫ k` and
`k ≫ p_U = p_R`, the identification `y^*c^*π^*M ≅ f_R^*p_R^*M` through `f_U^*p_U^*M` and
`f_R^*k^*p_U^*M` is the contraction along `(y ≫ c) ≫ π = f_R ≫ p_R`. -/
theorem modulePullback_map_comp_modulePullbackCompIso_eq_of_squares
    {W V P X U R : AlgebraicSpaces B S hS} (y : W ⟶ V) (c : V ⟶ P) (π : P ⟶ X) (fU : V ⟶ U)
    (pu : U ⟶ X) (fR : W ⟶ R) (k : R ⟶ U) (pr : R ⟶ X) (hc : c ≫ π = fU ≫ pu)
    (e : y ≫ fU = fR ≫ k) (hk : k ≫ pu = pr) (ht : (y ≫ c) ≫ π = fR ≫ pr)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    comp₂ ((modulePullback B S hS y).map ((modulePullbackCompIso B S hS c π).hom.app M))
      (comp₂ ((modulePullback B S hS y).map (pullbackTransport M hc))
        (comp₂ ((modulePullback B S hS y).map ((modulePullbackCompIso B S hS fU pu).inv.app M))
          (comp₂ ((modulePullbackCompIso B S hS y fU).hom.app ((modulePullback B S hS pu).obj M))
            (comp₂ (pullbackTransport ((modulePullback B S hS pu).obj M) e)
              (comp₂ ((modulePullbackCompIso B S hS fR k).inv.app
                  ((modulePullback B S hS pu).obj M))
                (comp₂ ((modulePullback B S hS fR).map
                    ((modulePullbackCompIso B S hS k pu).hom.app M))
                  ((modulePullback B S hS fR).map (pullbackTransport M hk)))))))) =
    comp₂ ((modulePullbackCompIso B S hS y c).hom.app ((modulePullback B S hS π).obj M))
      (comp₂ ((modulePullbackCompIso B S hS (y ≫ c) π).hom.app M)
        (comp₂ (pullbackTransport M ht) ((modulePullbackCompIso B S hS fR pr).inv.app M))) := by
  have e' : y ≫ fU ≫ pu = fR ≫ k ≫ pu := by rw [← Category.assoc, e, Category.assoc]
  have htt : pullbackTransport M (Category.assoc y c π) ≫
      pullbackTransport M (congrArg (y ≫ ·) hc : y ≫ c ≫ π = y ≫ fU ≫ pu) ≫
        pullbackTransport M e' ≫
          pullbackTransport M (congrArg (fR ≫ ·) hk : fR ≫ k ≫ pu = fR ≫ pr) =
      pullbackTransport M ht :=
    (congrArg (fun x => pullbackTransport M (Category.assoc y c π) ≫ x)
      (pullbackTransport_comp₃ B S hS M _ _ _ ((congrArg (y ≫ ·) hc).trans
        (e'.trans (congrArg (fR ≫ ·) hk))))).trans
      (pullbackTransport_comp M _ _ _)
  exact comp_eq_of_chart_contractions
    (x1 := (modulePullback B S hS y).map ((modulePullbackCompIso B S hS c π).hom.app M))
    (x2 := (modulePullback B S hS y).map (pullbackTransport M hc))
    (m1 := (modulePullback B S hS y).map ((modulePullbackCompIso B S hS fU pu).inv.app M))
    (c1 := (modulePullbackCompIso B S hS y fU).hom.app ((modulePullback B S hS pu).obj M))
    (t := pullbackTransport ((modulePullback B S hS pu).obj M) e)
    (c2 := (modulePullbackCompIso B S hS fR k).inv.app ((modulePullback B S hS pu).obj M))
    (c3 := (modulePullback B S hS fR).map ((modulePullbackCompIso B S hS k pu).hom.app M))
    (x3 := (modulePullback B S hS fR).map (pullbackTransport M hk))
    (g1 := (modulePullbackCompIso B S hS y c).hom.app ((modulePullback B S hS π).obj M))
    (g2 := (modulePullbackCompIso B S hS (y ≫ c) π).hom.app M)
    (tt := pullbackTransport M ht)
    (d4 := (modulePullbackCompIso B S hS fR pr).inv.app M)
    (d1 := (modulePullbackCompIso B S hS y (fU ≫ pu)).hom.app M)
    (t'' := pullbackTransport M e')
    (d3 := (modulePullbackCompIso B S hS fR (k ≫ pu)).inv.app M)
    (e1 := (modulePullbackCompIso B S hS y (c ≫ π)).hom.app M)
    (t1 := pullbackTransport M (congrArg (y ≫ ·) hc : y ≫ c ≫ π = y ≫ fU ≫ pu))
    (as := pullbackTransport M (Category.assoc y c π))
    (t2 := pullbackTransport M (congrArg (fR ≫ ·) hk : fR ≫ k ≫ pu = fR ≫ pr))
    (modulePullback_map_inv_comp_pullbackTransport_comp_eq y fU pu fR k e e' M)
    (modulePullback_map_pullbackTransport_comp_modulePullbackCompIso_hom y hc M)
    (modulePullback_map_modulePullbackCompIso_hom_comp_eq_comp_pullbackTransport y c π M)
    (modulePullbackCompIso_inv_app_comp_modulePullback_map_pullbackTransport fR hk M) htt

end Coherence

section RepresentedChart

attribute [local irreducible] CategoryTheory.yoneda

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The identification `g^*(M^a) ≅ (g^*M)^a` along equal morphisms**: for `g = g'`, the
identification along `g`, followed by the module attached to the identification
`g^*M = g'^*M`, is the transport of `M^a` along the represented morphisms followed by the
identification along `g'`. -/
theorem modulePullbackRepresentedQuasicoherentIso_hom_comp_map_eqToHom {V U : BigFppfOver B S hS}
    {g g' : V ⟶ U} (h : g = g')
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
          (eqToHom (congrArg (fun k => quasicoherentPullbackObj B S hS k M) h :
            quasicoherentPullbackObj B S hS g M = quasicoherentPullbackObj B S hS g' M))).hom =
      pullbackTransport (T := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩)
          (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
          (congrArg (representedSpaceMap B S hS) h :
            representedSpaceMap B S hS g = representedSpaceMap B S hS g') ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS g' M).hom := by
  subst h
  rw [eqToHom_refl, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- `AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso_comp` on the underlying
morphisms, with the inverse image along the composite reached by the comparison of Stacks 03LU
followed by the identification `eqToIso` of the two spellings of the composite. -/
theorem modulePullbackRepresentedQuasicoherentIso_comp_hom_trans_eqToIso
    {W V U : BigFppfOver B S hS} (h : W ⟶ V) (g : V ⟶ U)
    (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS h)
        (representedSpaceMap B S hS g) ≪≫ eqToIso (congrArg (modulePullback B S hS)
          (representedSpaceMap_comp B S hS h g))).hom.app
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS (h ≫ g) M).hom =
      (modulePullback B S hS (representedSpaceMap B S hS h)).map
          (modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS h
            (quasicoherentPullbackObj B S hS g M)).hom ≫
          ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
            (quasicoherentPullbackCompIso B S hS h g M).hom).hom :=
  congrArg Iso.hom (modulePullbackRepresentedQuasicoherentIso_comp B S hS h g M)

/-- The contraction of Stacks 03LU along `a ≫ b` followed by the transport to `ab`, on a module:
the contraction followed by `AlgebraicGeometry.Space.pullbackTransport`.  The composite in `hab`
is formed in the full subcategory of presheaves, as in
`AlgebraicGeometry.Space.representedSpaceMap_comp`. -/
theorem modulePullbackCompIso_trans_eqToIso_hom_app_eq_comp_pullbackTransport
    {T V U : AlgebraicSpaces B S hS} (a : T ⟶ V) (b : V ⟶ U) {ab : T ⟶ U}
    (hab : CategoryStruct.comp (obj := ObjectProperty.FullSubcategory
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)) a b = ab)
    (hab' : a ≫ b = ab) (G : Modules.{u, u} B S hS U.1 U.2) :
    (modulePullbackCompIso B S hS a b ≪≫
        eqToIso (congrArg (modulePullback B S hS) hab)).hom.app G =
      (modulePullbackCompIso B S hS a b).hom.app G ≫ pullbackTransport G hab' := by
  subst hab
  rfl

/-- The inverse of the contraction of Stacks 03LU along `a ≫ b` followed by the transport to
`ab`, on a module: the transport back followed by the inverse contraction. -/
theorem modulePullbackCompIso_trans_eqToIso_inv_app_eq_pullbackTransport_comp
    {T V U : AlgebraicSpaces B S hS} (a : T ⟶ V) (b : V ⟶ U) {ab : T ⟶ U}
    (hab : CategoryStruct.comp (obj := ObjectProperty.FullSubcategory
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)) a b = ab)
    (hab' : a ≫ b = ab) (G : Modules.{u, u} B S hS U.1 U.2) :
    (modulePullbackCompIso B S hS a b ≪≫
        eqToIso (congrArg (modulePullback B S hS) hab)).inv.app G =
      pullbackTransport G hab'.symm ≫ (modulePullbackCompIso B S hS a b).inv.app G := by
  subst hab
  rfl

/-- The contractions of Stacks 03LU followed by transports to given composites, along a
commutative square: the contraction along `a ≫ b` transported to `ab`, the transport along
`ab = cd` and the inverse of the contraction along `c ≫ d` transported to `cd` are the
contraction along `a ≫ b`, the transport along the square and the inverse contraction along
`c ≫ d`. -/
theorem modulePullbackCompIso_trans_eqToIso_hom_app_comp_pullbackTransport_comp_inv_app
    {T V U R : AlgebraicSpaces B S hS} (a : T ⟶ V) (b : V ⟶ U) (c : T ⟶ R) (d : R ⟶ U)
    {ab cd : T ⟶ U} (hab : CategoryStruct.comp (obj := ObjectProperty.FullSubcategory
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)) a b = ab)
    (hcd : CategoryStruct.comp (obj := ObjectProperty.FullSubcategory
      (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u => IsAlgebraicSpace B S hS F)) c d = cd)
    (e : ab = cd) (e' : a ≫ b = c ≫ d) (G : Modules.{u, u} B S hS U.1 U.2) :
    (modulePullbackCompIso B S hS a b ≪≫
        eqToIso (congrArg (modulePullback B S hS) hab)).hom.app G ≫
      pullbackTransport G e ≫
        (modulePullbackCompIso B S hS c d ≪≫
          eqToIso (congrArg (modulePullback B S hS) hcd)).inv.app G =
    (modulePullbackCompIso B S hS a b).hom.app G ≫ pullbackTransport G e' ≫
        (modulePullbackCompIso B S hS c d).inv.app G := by
  have hab' : a ≫ b = ab := hab
  have hcd' : c ≫ d = cd := hcd
  rw [modulePullbackCompIso_trans_eqToIso_hom_app_eq_comp_pullbackTransport a b hab hab' G,
    modulePullbackCompIso_trans_eqToIso_inv_app_eq_pullbackTransport_comp c d hcd hcd' G,
    Category.assoc, reassoc_of% (pullbackTransport_comp₃ B S hS G hab' e hcd'.symm e')]

/-- **The contractions of Stacks 03LU at represented morphisms along a commutative square**: the
contraction at the represented composite along `y ≫ f_U`, the transport along
`y ≫ f_U = f_R ≫ k` and the inverse contraction along `f_R ≫ k` are the contraction of the
represented morphisms, the transport along the square of represented morphisms and the inverse
contraction. -/
theorem representedModulePullbackCompIso_hom_app_comp_pullbackTransport_comp_inv_app
    {W V U R : BigFppfOver B S hS} (y : W ⟶ V) (fU : V ⟶ U) (fR : W ⟶ R) (k : R ⟶ U)
    (e : y ≫ fU = fR ≫ k)
    (e' : CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS y)
        (representedSpaceMap B S hS fU) =
      CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS fR)
        (representedSpaceMap B S hS k))
    (G : Modules.{u, u} B S hS (yoneda.obj U) (isAlgebraicSpace_yoneda B S hS U)) :
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS y)
        (representedSpaceMap B S hS fU) ≪≫ eqToIso (congrArg (modulePullback B S hS)
          (representedSpaceMap_comp B S hS y fU))).hom.app G ≫
      pullbackTransport (T := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
          (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) G
          (congrArg (representedSpaceMap B S hS) e :
            representedSpaceMap B S hS (y ≫ fU) = representedSpaceMap B S hS (fR ≫ k)) ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS fR)
          (representedSpaceMap B S hS k) ≪≫ eqToIso (congrArg (modulePullback B S hS)
            (representedSpaceMap_comp B S hS fR k))).inv.app G =
    (modulePullbackCompIso B S hS (representedSpaceMap B S hS y)
        (representedSpaceMap B S hS fU)).hom.app G ≫
      pullbackTransport (T := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
          (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩) G e' ≫
        (modulePullbackCompIso B S hS (representedSpaceMap B S hS fR)
          (representedSpaceMap B S hS k)).inv.app G :=
  modulePullbackCompIso_trans_eqToIso_hom_app_comp_pullbackTransport_comp_inv_app
    (representedSpaceMap B S hS y) (representedSpaceMap B S hS fU) (representedSpaceMap B S hS fR)
    (representedSpaceMap B S hS k) (representedSpaceMap_comp B S hS y fU)
    (representedSpaceMap_comp B S hS fR k) (congrArg (representedSpaceMap B S hS) e) e' G

/-- The abstract shape of
`AlgebraicGeometry.Space.modulePullback_map_modulePullbackRepresentedQuasicoherentIso_comp_chain`,
at variables. -/
private theorem comp_eq_of_represented_readings {D : Type*} [Category D]
    {Z0 Z1 Z2 Z3 Z4 Z5 Z6 Y1 Y2 Y3 Y4 Y5 X2 X3 : D}
    (a : Z0 ⟶ Z1) (b : Z1 ⟶ Z2) (φ1 : Z2 ⟶ Z3) (φ2 : Z3 ⟶ Z4) (φ3 : Z4 ⟶ Z5) (φ4 : Z5 ⟶ Z6)
    (c : Z0 ⟶ Y1) (p : Y1 ⟶ Y2) (ci : Y2 ⟶ Y3) (α : Y3 ⟶ Y4) (β : Y4 ⟶ Y5) (γ : Y5 ⟶ Z6)
    (r1 : Z0 ⟶ X2) (c2 : X2 ⟶ Z3) (t : X2 ⟶ X3) (c3 : X3 ⟶ Z4) (r2i : X3 ⟶ Y3) (r2 : Y3 ⟶ X3)
    (b2 : Y4 ⟶ Z5) (ψ : Z5 ⟶ Z4)
    (h1 : r1 ≫ c2 = a ≫ b ≫ φ1) (h2 : c2 ≫ φ2 = t ≫ c3) (h3 : r2 ≫ c3 = α ≫ b2 ≫ ψ)
    (h3' : ψ ≫ φ3 = 𝟙 _) (h3'' : r2i ≫ r2 = 𝟙 _) (h4 : β ≫ γ = b2 ≫ φ4)
    (hrep : r1 ≫ t ≫ r2i = c ≫ p ≫ ci) :
    comp₂ a (comp₂ b (comp₂ φ1 (comp₂ φ2 (comp₂ φ3 φ4)))) =
      comp₂ c (comp₂ p (comp₂ ci (comp₂ α (comp₂ β γ)))) := by
  simp only [comp₂_eq]
  have k1 : c3 ≫ φ3 = r2i ≫ α ≫ b2 := by
    calc c3 ≫ φ3 = (r2i ≫ r2) ≫ c3 ≫ φ3 := by rw [h3'', Category.id_comp]
      _ = r2i ≫ α ≫ b2 := by
        rw [Category.assoc, reassoc_of% h3, h3', Category.comp_id]
  rw [← reassoc_of% h1, reassoc_of% h2, reassoc_of% k1, h4, ← reassoc_of% hrep]

/-- **The identifications `g^*(M^a) ≅ (g^*M)^a` along a commutative square.**  For
`y ≫ f_U = f_R ≫ k` of the site and `pc : k^*N_U ⟶ N_R`, the identifications along `f_U` and `y`,
followed by the module attached to the chain `y^*f_U^*N_U ≅ f_R^*k^*N_U ⟶ f_R^*N_R` on schemes,
are the contraction of Stacks 03LU along the square followed by the pullback along `f_R` of the
identification along `k` and of the module attached to `pc`, and by the identification along
`f_R`. -/
theorem modulePullback_map_modulePullbackRepresentedQuasicoherentIso_comp_chain
    {W V U R : BigFppfOver B S hS} (y : W ⟶ V) (fU : V ⟶ U) (fR : W ⟶ R) (k : R ⟶ U)
    (e : y ≫ fU = fR ≫ k)
    (e' : CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS y)
        (representedSpaceMap B S hS fU) =
      CategoryStruct.comp (obj := AlgebraicSpaces B S hS) (representedSpaceMap B S hS fR)
        (representedSpaceMap B S hS k))
    (NU : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
    (NR : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj R).ringCatSheaf).FullSubcategory)
    (pc : quasicoherentPullbackObj B S hS k NU ⟶ NR) :
    comp₂ ((modulePullback B S hS (representedSpaceMap B S hS y)).map
        (modulePullbackRepresentedQuasicoherentIso B S hS fU NU).hom)
      (comp₂ (modulePullbackRepresentedQuasicoherentIso B S hS y
          (quasicoherentPullbackObj B S hS fU NU)).hom
        (comp₂ ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
          (quasicoherentPullbackCompIso B S hS y fU NU).hom).hom
          (comp₂ ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
            (eqToHom (congrArg (fun g => quasicoherentPullbackObj B S hS g NU) e :
              quasicoherentPullbackObj B S hS (y ≫ fU) NU =
                quasicoherentPullbackObj B S hS (fR ≫ k) NU))).hom
            (comp₂ ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
              (quasicoherentPullbackCompIso B S hS fR k NU).inv).hom
              ((representedQuasicoherentSchemeEquivalence B S hS W).functor.map
                (quasicoherentPullbackMap B S hS fR pc)).hom)))) =
    comp₂ ((modulePullbackCompIso B S hS (representedSpaceMap B S hS y)
          (representedSpaceMap B S hS fU)).hom.app
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj NU).obj)
      (comp₂ (pullbackTransport (T := ⟨yoneda.obj W, isAlgebraicSpace_yoneda B S hS W⟩)
          (X := ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj NU).obj e')
        (comp₂ ((modulePullbackCompIso B S hS (representedSpaceMap B S hS fR)
          (representedSpaceMap B S hS k)).inv.app
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj NU).obj)
          (comp₂ ((modulePullback B S hS (representedSpaceMap B S hS fR)).map
            (modulePullbackRepresentedQuasicoherentIso B S hS k NU).hom)
            (comp₂ ((modulePullback B S hS (representedSpaceMap B S hS fR)).map
              ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map pc).hom)
              (modulePullbackRepresentedQuasicoherentIso B S hS fR NR).hom)))) :=
  comp_eq_of_represented_readings _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (modulePullbackRepresentedQuasicoherentIso_comp_hom_trans_eqToIso y fU NU)
    (modulePullbackRepresentedQuasicoherentIso_hom_comp_map_eqToHom e NU)
    (modulePullbackRepresentedQuasicoherentIso_comp_hom_trans_eqToIso fR k NU)
    (congrArg (fun f => f.hom) ((representedQuasicoherentSchemeEquivalence B S hS W).functor.mapIso
      (quasicoherentPullbackCompIso B S hS fR k NU)).hom_inv_id)
    (Iso.inv_hom_id_app _ _)
    (modulePullbackRepresentedQuasicoherentIso_naturality B S hS fR pc)
    (representedModulePullbackCompIso_hom_app_comp_pullbackTransport_comp_inv_app y fU fR k e e' _)

end RepresentedChart

end AlgebraicGeometry.Space

end
